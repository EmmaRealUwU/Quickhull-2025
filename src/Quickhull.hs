{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P


-- Points and correspondingLines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point --finds the point with the largest and smallest x component
      p1 = the $ fold1All (\point1 point2 -> if fst point1 <= fst point2 then point1 else point2) points 
      p2 = the $ fold1All (\point1 point2 -> if fst point1 >= fst point2 then point1 else point2) points 

      isUpper :: Acc (Vector Bool) --maps whether points are left of p1 p2
      isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

      isLower :: Acc (Vector Bool) --maps whether points are right of p1 p2 (== left of p2 p1)
      isLower = map (pointIsLeftOfLine (T2 p2 p1)) points

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = T2 relativeIndices summedLeft
        where
          flagsToNumbers :: Acc (Vector Int) --sets the flags to one
          flagsToNumbers = map (\x -> if x then 1 else 0) isUpper

          relativeIndices :: Acc (Vector Int) --sets first flag to 1, every next flag to +1
          relativeIndices = scanl1 (+) flagsToNumbers

          summedLeft:: Acc (Scalar Int) --counts all flags
          summedLeft = sum flagsToNumbers 


      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = T2 relativeIndices summedRight
        where
          flagsToNumbers :: Acc (Vector Int) --sets the flags to one
          flagsToNumbers = map (\x -> if x then 1 else 0) isLower

          relativeIndices :: Acc (Vector Int) --sets first flag to 1, every next flag to +1
          relativeIndices = scanl1 (+) flagsToNumbers

          summedRight:: Acc (Scalar Int) --counts all flags
          summedRight = sum flagsToNumbers 

      destination :: Acc (Vector (Maybe DIM1))
      destination = imap toDestination points
        where
          toDestination :: Exp DIM1 -> Exp Point -> Exp (Maybe DIM1)
          toDestination index point = ifThenElse  (point == p1)     (Just_ $ constant $ Z:. 0) --p1 takes the first index in the resulting array
                                      (ifThenElse (point == p2)     (Just_ $ lift $ Z:. the countUpper + 1) --p2 takes the index right after the section of upper points in the resulting array
                                      (ifThenElse (isUpper ! index) (Just_ $ lift $ Z:. offsetUpper ! index) --upper points take the index that is the same as their offset
                                      (ifThenElse (isLower ! index) (Just_ $ lift $ Z:. offsetLower ! index + the countUpper + 1) --lower points take the index equal to its offset after p2
                                      Nothing_ --if a point is not p1, p2, upper, or lower, then it must be on the line p1 p2 and thus has no place in the resulting array
                                      )))

      newPoints :: Acc (Vector Point)
      newPoints = permute const (fill (I1 $ the countUpper + the countLower + 3) p1) (destination!) points
      --permute using \x -> index x of destination, over an array of size countupper + countlower + 3, default value p1

      headFlags :: Acc (Vector Bool) --array where at each index with p1 or p2, there is a flag to indicate it
      headFlags = map (\x -> x == p1 || x == p2) newPoints
  in
  T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) = T2 (map fst sortedSet) (map snd sortedSet)
  where
    --creates a list of the line-segments the points in those spots belong to, based on the given list of flags
    --the decided points just have the same point twice
    --vb: [(p1,p1), (p1,p2), (p1,p2),(p1,p2), (p2,p2), (p2,p3), (p2,p3), (p3,p3), (p3,p1), (p3,p1), (p1,p1)]
    -- :: Vector(Bool) -> vector(point,point)
    correspondingLines flags = zip (propagateL flags points) ( propagateR flags points)

    --empty :: Elt a => Acc (Vector a)
    --an empty vector with the same number of elements as points
    fillEasy :: Elt a => Exp a -> Acc (Vector a)
    fillEasy  = fill ( I1 $ length points)

    --calculates the points furthest from the line segments 
    -- and flags it as a new hullpoint
    --the headflags are shifted back and forth to keep them in the correct place
    newHeadFlags = shiftHeadFlagsR $ map (\(T3 _ _ flag) -> flag) $ segmentedScanr1 --scans in the opposite direction from Distance
      (\ (T3 pointNotFound oldDistance _) (T3 _ currentDistance currentHeadFlag) -> --pointNotFound is True as long as we are still looking, so only the first point gets flagged each segment
        if pointNotFound && oldDistance > currentDistance --the segment allways starts with the highest distance, so when the distance goes down, we have found the furthestpoint
          then T3 (lift False) currentDistance $ lift True --only supposed to happen the first time in the segment 0.0
          else T3 pointNotFound currentDistance currentHeadFlag) --
      (shiftHeadFlagsL headFlags) (zip3 (fillEasy $ lift True) distances $ shiftHeadFlagsL headFlags)
      where
      --creates a list of the distance each point has from its closest line(based on the headflags)
      --using a leftscan, creates a list of the furthest distance from its line a point has had in that segment.
      --meaning the rightmost element in a segment has the furthest distance any point in the segment has from the line
      --vb: [7,7,7,7,5,5,4,2,10,10,8,8,8]
        distances :: Acc (Vector Int)
        distances =  map (snd P.. fst) $ segmentedScanl1 setDistance headFlags (zip points $ correspondingLines headFlags) --(T2 headFlags points)
          where
          --setDistance :: Exp (Point, Line) -> Exp (Point, Line) -> Exp (Point, Line)
          --r and i may be turned around?
            setDistance (T2 (T2  _ maxDistance) _) (T2 (T2 a b) aLine)  =  T2 ( T2 b (max distance maxDistance)) aLine
              where distance = nonNormalizedDistance (lift aLine) $ lift (a, b)



    --calculates the following for each point:
    --(relativeIndex, = if the point is kept, this is the index of where it will be in its segment
    --keepPointFlag, = weather or not we keep the point, or discard it(bacause it is definitely NOT on the convex hull)
    --segmentScore) = the index of the headflag of the segment the point belongs to
    --the final index can be accieved by adding the relativeindex to the segmentscore
    flaggedRelativeIndex :: Acc (Vector (Int, Bool, Int))
    flaggedRelativeIndex = zip3 (map (\(T3 (T3 x _ _) _ _ ) -> x) rightRelativeIndex) (map (\(T3 (T3 _ x _) _ _ ) -> x) rightRelativeIndex) segmentScore
      where

        --((relativeindex, stayflag, point) highestIndex, line)
        --relativeIndex starts at 1
        leftRelativeIndex :: Acc (Vector ((Int, Bool, Point), Int, Line))
        leftRelativeIndex =
          let
            --sets the relative-index of all the points left of the line between the newHullPoint and the point left of the newHullPoints
            --and flags these points as 'keepers'
            --newHullPoint gets skipped
            leftRelativeIndex1 :: Acc (Vector (Int, Bool, Point))
            leftRelativeIndex1 = map (\(T4 i f p _) -> T3 i f p) $ segmentedScanl1
              (\(T4 lastIndex _ _ _) (T4 _ flag point line) ->
                if pointIsLeftOfLine line point
                  then T4 (lift $ 1 + lastIndex) (lift True) point line
                  else T4 lastIndex flag point line) --ensures the oldHullPoints stay at index 0 and get flagged true
              headFlags $ zip4 (fillEasy 0)  headFlags points leftLines
              --creates a list where every segment contains the line on the left side of the newHullPoint
              --bv: [p1, x, x, np, x, x, x, p2]
              --    [(p-1,pn-1), (p1, pn), (p1, pn), (p1, pn), (p1, pn), (p1, pn), (p1, pn), (p1, pn)]
              where leftLines = propagateL (shiftHeadFlagsR headFlags) $ correspondingLines newHeadFlags
              --newHullPoint does not have (nHP,nHP) as its corresponding line segment
              --no 'neutral' line segments excpet p1
          in
          --find, flag and index the newHullPoint as well
          --and give the highest index of each segment, oldHullPoints will have a highest index of 0
          segmentedScanr1
            (\(T3 _ highestIndex _) (T3 (T3 currIndex flag point) _ line) ->
              T3
                (T3
                  (if point == fst line && flag == lift False --if the point is the newHullPoint, give it an index one higher than the highest index in that segment
                    then max (currIndex +1) highestIndex
                    else currIndex)
                  (if point == fst line then lift True else flag)
                  point)
                (if currIndex > highestIndex then currIndex + 1 else highestIndex) --set the new highest index
                line)
          headFlags $ zip3 leftRelativeIndex1 (fillEasy 0) rightLines
          ----creates a list where every segment contains the line on the the right side of the newHullPoint
          where rightLines = propagateR (shiftHeadFlagsL headFlags) $ correspondingLines newHeadFlags

          --each segment needs to start one higher
          --((relativeIndex, stayflag, point) highestIndex, line)
        rightRelativeIndex = segmentedScanl1 pickRelativeIndex headFlags leftRelativeIndex
          where
            --give the points left of the line a new index & flag, keep the others as-is
            pickRelativeIndex :: Exp ((Int, Bool, Point), Int, Line) -> Exp ((Int, Bool, Point), Int, Line) -> Exp ((Int, Bool, Point), Int, Line)
            pickRelativeIndex (T3 _ prevHighestIndex _) (T3 (T3 currIndex flag point) currHighestIndex line) =
                if flag == lift False && pointIsLeftOfLine line point
                  then  T3 (T3 (1 + highestIndex) (lift True) point) (1 + highestIndex) line
                  else T3 (T3 currIndex flag point) highestIndex line
              where highestIndex = max prevHighestIndex currHighestIndex --should do nothing? could just be currHighest Index?


        --makes list of segmentscores that can be added to the relativeIndex to make the finalindex
        --starts at 0?
        segmentScore :: Acc (Vector Int)
        segmentScore = map (\(T3 _ _ s) -> s - 1) $ scanl1
          (\(T3 prevFlag prevHighestIndex prevSegmentScore) ( T3 currFlag highestIndex _) ->
            if currFlag then
              if prevFlag then T3 currFlag highestIndex (prevSegmentScore + 1)
              else T3 currFlag highestIndex (prevHighestIndex + prevSegmentScore + 1)
            else T3 currFlag highestIndex prevSegmentScore)
          $ zip3 headFlags (map (\(T3 _ highestIndex _ ) -> highestIndex) rightRelativeIndex) (fillEasy 0)

          --(\(T2 _ highestSegScore) (T2 flag highestRelativeIndex) -> 
            --if flag -- && highestRelativeIndex > 0
             -- then T2 flag $ highestSegScore + highestRelativeIndex + 1 
             -- else T2 flag highestSegScore) 
          -- $ zip headFlags $
           -- init $ scanl (\prev curr -> curr) 0 (propagateL (shiftHeadFlagsL headFlags) -- puts the highest index of the previous segment in the next one
             -- $ map (\(T3 _ highestIndex _ ) -> highestIndex) rightRelativeIndex) --take the list of highest indexes


    --turn the ralativeIndex into a proper index
    flaggedTargetIndex :: Acc (Vector (Int, Bool))
    flaggedTargetIndex = map (\(T3 relativeIndex keepPointFlag segmentScore) -> T2 (relativeIndex + segmentScore) keepPointFlag) flaggedRelativeIndex

    newLength = the $  maximum $ map fst flaggedTargetIndex

    sortedSet :: Acc( Vector (Bool, Point))
    sortedSet = permute
      (\a b -> a) --combination function
      (fill (I1 (newLength))  $ T2 (lift False) (T2 0 0))
    --index permutation function
      (\currentIndex -> if snd (flaggedTargetIndex ! currentIndex) then lift $ Just (I1 $ fst (flaggedTargetIndex ! currentIndex)) else Nothing_ )
      (zip newHeadFlags points) --source values (should be in correct order?)








-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull input = init $ asnd $ awhile undecidedPoints partition (initialPartition input)
  where
    undecidedPoints :: Acc SegmentedPoints -> Acc (Scalar Bool)
    undecidedPoints (T2 headFlags points) = foldAll (\x y -> if y && x then lift False else lift True) (lift False) headFlags


-- Helper functions
-- ----------------

--copies the values from left TO right
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL flag val = map snd $ scanl1 newVal $ zip flag val
  where
    newVal :: Elt a => Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
    newVal prev cur = ifThenElse (fst cur)  cur prev

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR flag val = map snd $ scanr1 newVal $ zip flag val
  where
    newVal :: Elt a => Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
    newVal cur = ifThenElse (fst cur)  cur


--shifts flags TO the left
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL vec = tail $ scanr const (lift True) vec

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR vec = init $ scanl (\prev curr -> curr) (lift True) vec

--why is it like this, why does left mean two different things for different functions?
--this is so stupid

--scans a function over a vector in segments indicated by the headflags, treating each segment after a flag as its own vector
--scans from left TO right
segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f headFlags points = map snd $ scanl1 (segmented f) $ zip headFlags points

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f headFlags points = map snd $ scanr1 (flip (segmented (flip f))) $ zip headFlags points



-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))

