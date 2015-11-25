module TwoThreeTree

import StdEnv, StdLib, GenEq

:: T23 a = Empty
         | N2 (T23 a) a (T23 a)
         | N3 (T23 a) a (T23 a) a (T23 a)
         
:: RT23 a = REmpty
          | RN2 (RT23 a) a (RT23 a)
          | RN3 (RT23 a) a (RT23 a) a (RT23 a)
          | RN4 (RT23 a) a (RT23 a) a (RT23 a) a (RT23 a)

:: KeyVal k v = KV k v

derive gEq T23, RT23, Maybe, KeyVal

EmptyInt :: T23 Int
EmptyInt = Empty

REmptyInt :: RT23 Int
REmptyInt = REmpty

EmptyString :: T23 String
EmptyString = Empty

EmptyChar :: T23 Char
EmptyChar = Empty

t23_to_rt23 :: (T23 a) -> RT23 a
t23_to_rt23 Empty = REmpty
t23_to_rt23 (N2 p1 v1 p2) = RN2 (t23_to_rt23 p1) v1 (t23_to_rt23 p2)
t23_to_rt23 (N3 p1 v1 p2 v2 p3) = RN3 (t23_to_rt23 p1) v1 (t23_to_rt23 p2) v2 (t23_to_rt23 p3)

rt23_to_t23 :: (RT23 a) -> Maybe (T23 a)
rt23_to_t23 REmpty = Just Empty
rt23_to_t23 three
	| contains_RN4 three == True = Nothing
rt23_to_t23 (RN2 p1 v1 p2) = Just (N2 (fromJust(rt23_to_t23 p1)) v1 (fromJust(rt23_to_t23 p2)))
rt23_to_t23 (RN3 p1 v1 p2 v2 p3) = Just (N3 (fromJust(rt23_to_t23 p1)) v1 (fromJust(rt23_to_t23 p2)) v2 (fromJust(rt23_to_t23 p3)))

contains_RN4 :: (RT23 a) -> Bool
contains_RN4 (RN4 _ _ _ _ _ _ _) = True
contains_RN4 (RN2 p1 _ p2) = contains_RN4 p1 || contains_RN4 p2
contains_RN4 (RN3 p1 _ p2 _ p3) = contains_RN4 p1 || contains_RN4 p2 || contains_RN4 p2
contains_RN4 _ = False

t23_empty :: T23 a
t23_empty = Empty

t23_lookup :: a (T23 a) -> Maybe a | Eq a & Ord a
t23_lookup _ Empty = Nothing
t23_lookup value (N2 p1 v1 p2)
	| value == v1 = Just v1
	| value < v1 = t23_lookup value p1
	| otherwise = t23_lookup value p2
t23_lookup value (N3 p1 v1 p2 v2 p3)
	| value == v1 = Just v1
	| value == v2 = Just v2
	| value < v1 = t23_lookup value p1
	| value < v2 = t23_lookup value p2
	| otherwise = t23_lookup value p3

rt23_propagateSplit :: (RT23 a) -> RT23 a
rt23_propagateSplit REmpty = REmpty
rt23_propagateSplit (RN2 (RN4 p1_ v1_ p2_ v2_ p3_ v3_ p4_) v1 p2) = RN3 (RN2 p1_ v1_ p2_) v2_ (RN2 p3_ v3_ p4_) v1 p2
rt23_propagateSplit (RN2 p1 v1 (RN4 p1_ v1_ p2_ v2_ p3_ v3_ p4_)) = RN3 p1 v1 (RN2 p1_ v1_ p2_) v2_ (RN2 p3_ v3_ p4_)
rt23_propagateSplit (RN2 p1 v1 p2) = (RN2 (rt23_propagateSplit p1) v1 (rt23_propagateSplit p2))
rt23_propagateSplit (RN3 (RN4 p1_ v1_ p2_ v2_ p3_ v3_ p4_) v1 p2 v2 p3) = RN4 (RN2 p1_ v1_ p2_) v2_ (RN2 p3_ v3_ p4_) v1 p2 v2 p3
rt23_propagateSplit (RN3 p1 v1 (RN4 p1_ v1_ p2_ v2_ p3_ v3_ p4_) v2 p3) = RN4 p1 v1 (RN2 p1_ v1_ p2_) v2_ (RN2 p3_ v3_ p4_) v2 p3
rt23_propagateSplit (RN3 p1 v1 p2 v2 (RN4 p1_ v1_ p2_ v2_ p3_ v3_ p4_)) = RN4 p1 v1 p2 v2 (RN2 p1_ v1_ p2_) v3_ (RN2 p3_ v3_ p4_)
rt23_propagateSplit (RN3 p1 v1 p2 v2 p3) = RN3 (rt23_propagateSplit p1) v1 (rt23_propagateSplit p2) v2 (rt23_propagateSplit p3)
rt23_propagateSplit (RN4 p1 v1 p2 v2 p3 v3 p4) = RN2 (RN2 p1 v1 p2) v2 (RN2 p3 v3 p4)
