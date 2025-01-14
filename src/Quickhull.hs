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


-- Points and lines in two-dimensional space
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
      p1, p2 :: Exp Point
      p1 = error "TODO: locate the left-most point"
      p2 = error "TODO: locate the right-most point"

      isUpper :: Acc (Vector Bool)
      isUpper = error "TODO: determine which points lie above the line (p₁, p₂)"

      isLower :: Acc (Vector Bool)
      isLower = error "TODO: determine which points lie below the line (p₁, p₂)"

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = error "TODO: number of points above the line and their relative index"

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = error "TODO: number of points below the line and their relative index"

      destination :: Acc (Vector (Maybe DIM1))
      destination = error "TODO: compute the index in the result array for each point (if it is present)"

      newPoints :: Acc (Vector Point)
      newPoints = error "TODO: place each point into its corresponding segment of the result"

      headFlags :: Acc (Vector Bool)
      headFlags = error "TODO: create head flags array demarcating the initial segments"
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
    --the lines for the given flags/points
    lines flags = zip (propagateL flags points) ( propagateR flags points)
    

    distances :: Acc (Vector Int) --sets all the distances from the closest line
    distances =  map (snd P.. fst) $ segmentedScanl1 setDistance headFlags (zip points $ lines headFlags) --(T2 headFlags points)
      where 
        setDistance :: Exp (Point, Line) -> Exp (Point, Line) -> Exp (Point, Line)
        --r and i may be turned around
        setDistance (T2 (T2  _ maxDistance) _) (T2 (T2 a b) aLine)  =  T2 ( T2 b (max distance maxDistance)) aLine
          where distance = nonNormalizedDistance (lift aLine) $ lift (a, b)

    --shifts the headflags back and forth to get the new flags in the correct place
    -- ~boogie woogie~
    newHeadFlags = shiftHeadFlagsR $ map snd $ segmentedScanr1 
      (\(T2 prevDistance prevHeadFlag) (T2 currDistance currHeadFlag) -> 
        if prevDistance > currDistance then T2 currDistance $ lift True else T2 currDistance currHeadFlag) (shiftHeadFlagsL headFlags) (zip distances $ shiftHeadFlagsL headFlags)
    -- > used to be <

    --all points have a corresponding relative index and a ?segmentnr?
    --(relativeIndex, keepPointFlag, segmentScore)
    flaggedRelativeIndex :: Acc (Vector (Int, Bool, Int))
    flaggedRelativeIndex =
      let
          fill' :: Elt a => Exp a -> Acc (Vector a)
          fill' = fill ( I1 $  length points)

          leftRelativeIndex1 :: Acc (Vector (Int, Bool, Point))
          leftRelativeIndex1 = 
            map (\(T4 i f p l) -> (T3 i f p)) $ segmentedScanl1 (\(T4 lastIndex _ _ _) (T4 _ flag point line) -> 
                          if pointIsLeftOfLine line point 
                            then T4 (lift $ 1 + lastIndex) (lift True) point line 
                            else T4 lastIndex flag point line) --ensures 
            headFlags $ zip4 (fill' 0) headFlags points (propagateL (shiftHeadFlagsR headFlags) $ lines newHeadFlags) --Pn does not have have pn,pn as linesegment

        --find, flag and index the newpoint
        --((relativeindex, stayflag, point) highestIndex, line)
          leftRelativeIndex2 :: Acc (Vector ((Int, Bool, Point), Int, Line))
          leftRelativeIndex2 = 
            segmentedScanr1 
            (\(T3 _ highestIndex _) (T3 (T3 currIndex flag point) _ line) -> 
                T3 (T3 (if point == fst line && flag == lift False then max (currIndex +1) highestIndex else currIndex) 
                (if point == fst line then lift True else flag) point) 
                (if currIndex > highestIndex then currIndex + 1 else highestIndex) line)
            headFlags $ zip3 leftRelativeIndex1 ( fill' 0) (propagateR (shiftHeadFlagsL headFlags) $ lines newHeadFlags) --add new lines

          --each segment needs to start one higher
          --((index, stayflag, point) highestIndex, line)
          rightRelativeIndex = 
            let
              pickRelativeIndex :: Exp ((Int, Bool, Point), Int, Line) -> Exp ((Int, Bool, Point), Int, Line) -> Exp ((Int, Bool, Point), Int, Line)
              pickRelativeIndex (T3 _ prevHighestIndex _) (T3 (T3 currIndex flag point) currHighestIndex line) = 
                  if flag == lift False && pointIsLeftOfLine line point 
                    then  T3 (T3 (1 + highestIndex) (lift True) point) (1 + highestIndex) line
                    else T3 (T3 currIndex flag point) highestIndex line 
                where highestIndex = max prevHighestIndex currHighestIndex --should do nothing? could just be currHighest Index?
            in
            segmentedScanl1 pickRelativeIndex headFlags leftRelativeIndex2 
          
          --makes list of vectorscores that can be added to the relativeIndex to make the finalindex
          segmentScore = map snd $ scanl1 
            (\(T2 _ highestSegScore) (T2 flag highestRelativeIndex) -> if flag then T2 flag $ highestSegScore + highestRelativeIndex + 1 else T2 flag highestSegScore) 
            $ zip headFlags $
            propagateL headFlags (propagateL (shiftHeadFlagsL headFlags) 
            $ map (\(T3 _ highestIndex _ ) -> highestIndex) rightRelativeIndex)

      in
      zip3 (map (\(T3 (T3 x _ _) _ _ ) -> x) rightRelativeIndex) (map (\(T3 (T3 _ x _) _ _ ) -> x) rightRelativeIndex) segmentScore

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

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL flag val = map snd $ scanl1 newVal valueWithFlag
  where
    valueWithFlag = zip flag val
    newVal :: Elt a => Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
    newVal prev cur = ifThenElse (fst cur)  cur prev

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR flag val = map snd $ scanr1 newVal valueWithFlag
  where
    valueWithFlag = zip flag val
    newVal :: Elt a => Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
    newVal cur prev = ifThenElse (fst cur)  cur prev

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL vec = tail $ scanr (\curr prev -> curr) (lift True) vec

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR vec = init $ scanl (\prev curr -> curr) (lift True) vec

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 func headFlags points = 
  let 
    zipped = zip headFlags points                   --zip the flags to the points
    zippedAndScanned = scanl1 (segmented func) zipped    --scan using the function working only on segments
    scanned = map snd zippedAndScanned                    --map snd over the zipped and scanned array, to return only the points
  in scanned

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 func headFlags points = 
  let 
    zipped = zip headFlags points                --zip the flags to the points
    zippedAndScanned = scanr1 (flip (segmented(flip func))) zipped   --scan using the function working only on segments
    scanned = map snd zippedAndScanned                   --map snd over the zipped and scanned array, to return only the points
  in scanned


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

