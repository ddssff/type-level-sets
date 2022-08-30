{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType #-}

module Data.Type.List
  ( Cmp, Filter, Flag(..), (:++), Sort, MemberP, NonMember, Nub, (:\),
    SubtractSortedLists, IntersectSortedLists, UnionLists, AsSet, IsSet
  ) where

import GHC.TypeLits
import Data.Type.Bool
import Data.Type.Equality
import Data.Proxy (Proxy(Proxy))

{-| Open-family for the ordering operation in the sort -}

type family Cmp (a :: k) (b :: k) :: Ordering

type instance Cmp (k :: Symbol) (k' :: Symbol) = CmpSymbol k k'

data Flag = FMin | FMax

type family Filter (f :: Flag) (p :: k) (xs :: [k]) :: [k] where
  Filter f p '[]       = '[]
  Filter FMin p (x ': xs) = If (Cmp x p == LT) (x ': (Filter FMin p xs)) (Filter FMin p xs)
  Filter FMax p (x ': xs) = If (Cmp x p == GT || Cmp x p == EQ) (x ': (Filter FMax p xs)) (Filter FMax p xs)

{-| List append (essentially set disjoint union) -}
type family (:++) (x :: [k]) (y :: [k]) :: [k] where
            '[]       :++ xs = xs
            (x ': xs) :++ ys = x ': (xs :++ ys)

infixr 5 :++

{-| Type-level quick sort for normalising the representation of sets -}
type family Sort (xs :: [k]) :: [k] where
  Sort '[] = '[]
  Sort (x ': xs) = ((Sort (Filter FMin x xs)) :++ '[x]) :++ (Sort (Filter FMax x xs))

-- | Type level type list membership predicate: does the type 'a' show up in the
--   type list 's'?
--type MemberP :: k -> [k] -> Bool
type family MemberP a s :: Bool where
  MemberP a '[]      = False
  MemberP a (a ': s) = True
  MemberP a (b ': s) = MemberP a s

type NonMember a s = MemberP a s ~ False

{-| Remove duplicates from a sorted list -}
type family Nub t where
    Nub '[]           = '[]
    Nub '[e]          = '[e]
    Nub (e ': e ': s) = Nub (e ': s)
    Nub (e ': f ': s) = e ': Nub (f ': s)

{-| Delete elements from a set -}
type family (m :: [k]) :\ (x :: k) :: [k] where
     '[]       :\ x = '[]
     (x ': xs) :\ x = xs :\ x
     (y ': xs) :\ x = y ': (xs :\ x)

type family DeleteFromList (e :: elem) (list :: [elem]) where
    DeleteFromList elem '[] = '[]
    DeleteFromList elem (x ': xs) = If (Cmp elem x == EQ)
                                       xs
                                       (x ': DeleteFromList elem xs)

--     > :kind! SubtractSortedLists '["A", "C", "D"] ('["C"])
--     SubtractSortedLists '["A", "C", "D"] ('["C"]) :: [Symbol]
--     = '["A", "D"]
type family SubtractSortedLists (xs :: [k]) (ys :: [k]) where
  SubtractSortedLists (xs :: [k]) ('[] :: [k]) = xs
  SubtractSortedLists '[] ys = '[]
  SubtractSortedLists (x ': xs) ys =
    If (MemberP x ys) '[] '[x] :++ SubtractSortedLists xs ys

--     > :kind! IntersectSortedLists '["A", "C", "D"] ('["C"])
--     IntersectSortedLists '["A", "C", "D"] ('["C"]) :: [Symbol]
--     = '["C"]
type family IntersectSortedLists (xs :: [k]) (ys :: [k]) where
  IntersectSortedLists '[] ys = '[]
  IntersectSortedLists xs '[] = '[]
  IntersectSortedLists (x ': xs) ys =
    If (MemberP x ys) '[x] '[] :++ IntersectSortedLists xs ys
{-- Union --}

{-| Union of sets -}
type UnionLists s t = Nub (Sort (s :++ t))

{-| At the type level, normalise the list form to the set form -}
type AsSet s = Nub (Sort s)

{-| Predicate to check if in the set form -}
type IsSet s = (s ~ Nub (Sort s))
