{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType #-}

module Data.Type.Set (Set(Empty, Ext), ToSet, Element, NotElement,
                      Union, Insert, Unionable, union, quicksort, append,
                      Sortable, Split(..), Nubable(..), asSet, Subset(..),
                      Delete, Difference, Intersection, remove, Remove, Elem(..), Member(..), SetProperties,
                      module Data.Type.List, Proxy(Proxy)) where

import Data.Type.Bool
import Data.Type.Equality
import Data.Type.List
import Data.Proxy (Proxy(Proxy))

-- Value-level 'Set' representation,  essentially a list
--type Set :: [k] -> Type
data Set (n :: [k]) where
    {--| Construct an empty set -}
    Empty :: Set '[]
    {--| Extend a set with an element -}
    Ext :: e -> Set s -> Set (e ': s)

instance Show (Set '[]) where
    show Empty = "{}"

instance (Show e, Show' (Set s)) => Show (Set (e ': s)) where
    show (Ext e s) = "{" ++ show e ++ (show' s) ++ "}"

class Show' t where
    show' :: t -> String
instance Show' (Set '[]) where
    show' Empty = ""
instance (Show' (Set s), Show e) => Show' (Set (e ': s)) where
    show' (Ext e s) = ", " ++ show e ++ (show' s)

instance Eq (Set '[]) where
  (==) _ _ = True
instance (Eq e, Eq (Set s)) => Eq (Set (e ': s)) where
    (Ext e m) == (Ext e' m') = e == e' && m == m'

instance Ord (Set '[]) where
  compare _ _ = EQ
instance (Ord a, Ord (Set s)) => Ord (Set (a ': s)) where
  compare (Ext a as) (Ext a' as') = case compare a a' of
    EQ ->
      compare as as'

    other ->
      other

-- | At the type level, normalise the list form to the set form
--
--     > :kind! ToSet ["B", "B", "A"]
--     ToSet ["B", "B", "A"] :: *
--     = Set '["A", "B"]
type ToSet xs = Set (AsSet xs)

type family ElementP x s where
  ElementP x (Set '[]) = 'False
  ElementP x (Set (x ': xs)) = 'True
  ElementP x (Set (y ': xs)) = ElementP x (Set xs)

-- | Set membership constraints
type Element x s = ElementP x s ~ 'True
type NotElement x s = ElementP x s ~ 'False

type Delete x xs = Difference xs (ToSet '[x])

-- | > :kind! Difference (Set '["A", "B"]) (Set '["B"])
-- Difference (Set '["A", "B"]) (Set '["B"]) :: *
-- = Set '["A"]
type family Difference a b where
  Difference (Set xs) (Set ys) = Set (SubtractSortedLists xs ys)

type family Union a b where
  Union (Set '[]) s = s
  Union s (Set '[]) = s
  Union (Set xs) (Set ys) = ToSet (xs :++ ys)
  -- Union (Set (x ': xs)) (Set ys) = Union (Set xs) (Set (If (MemberP x ys) ys (x ': ys)))
  -- Union (Set xs) (Set ys) = Set (UnionLists xs ys)

type family Intersection a b where
  Intersection (Set '[]) s = Set '[]
  Intersection s (Set '[]) = Set '[]
  Intersection (Set (x ': xs)) (Set ys) =
    Union (If (MemberP x ys) (Set '[x]) (Set '[])) (Intersection (Set xs) (Difference (Set ys) (Set '[x])))

type Insert x s = Union (Set '[x]) s

{-| Value-level counterpart to the type-level 'Nub'
    Note: the value-level case for equal types is not define here,
          but should be given per-application, e.g., custom 'merging' behaviour may be required -}

class Nubable t where
    nub :: Set t -> Set (Nub t)

instance Nubable '[] where
    nub Empty = Empty

instance Nubable '[e] where
    nub (Ext x Empty) = Ext x Empty

instance Nubable (e ': s) => Nubable (e ': e ': s) where
    nub (Ext _ (Ext e s)) = nub (Ext e s)

instance {-# OVERLAPS #-} (Nub (e ': f ': s) ~ (e ': Nub (f ': s)),
              Nubable (f ': s)) => Nubable (e ': f ': s) where
    nub (Ext e (Ext f s)) = Ext e (nub (Ext f s))

class Conder g where
    cond :: Proxy g -> Set s -> Set t -> Set (If g s t)

instance Conder 'True where
    cond _ s _ = s

instance Conder 'False where
    cond _ _ t = t

{- Filter out the elements less-than or greater-than-or-equal to the pivot -}
class FilterV (f::Flag) p xs where
    filterV :: Proxy f -> p -> Set xs -> Set (Filter f p xs)

instance FilterV f p '[] where
    filterV _ _ Empty      = Empty

instance (Conder ((Cmp x p) == 'LT), FilterV 'FMin p xs) => FilterV 'FMin p (x ': xs) where
    filterV f@Proxy p (Ext x xs) = cond (Proxy::(Proxy ((Cmp x p) == 'LT)))
                                        (Ext x (filterV f p xs)) (filterV f p xs)

instance (Conder (((Cmp x p) == 'GT) || ((Cmp x p) == 'EQ)), FilterV 'FMax p xs) => FilterV 'FMax p (x ': xs) where
    filterV f@Proxy p (Ext x xs) = cond (Proxy::(Proxy (((Cmp x p) == 'GT) || ((Cmp x p) == 'EQ))))
                                        (Ext x (filterV f p xs)) (filterV f p xs)

{-| Access the value at a type present in a set. -}
class Elem a s where
  project :: Proxy a -> Set s -> a

instance {-# OVERLAPS #-} Elem a (a ': s) where
  project _ (Ext x _)  = x

instance {-# OVERLAPPABLE #-} Elem a s => Elem a (b ': s) where
  project p (Ext _ xs) = project p xs

-- | Value level type list membership predicate: does the type 'a' show up in
--   the type list 's'?
class Member a s where
  member :: Proxy a -> Set s -> Bool

instance Member a '[] where
  member _ Empty = False

instance {-# OVERLAPS #-} Member a (a ': s) where
  member _ (Ext _ _)  = True

instance {-# OVERLAPPABLE #-} Member a s => Member a (b ': s) where
  member p (Ext _ xs) = member p xs

append :: Set s -> Set t -> Set (s :++ t)
append Empty x = x
append (Ext e xs) ys = Ext e (append xs ys)

{-| Construct a subsetset 's' from a superset 't' -}
class Subset s t where
   subset :: Set t -> Set s

instance Subset '[] '[] where
   subset _ = Empty

instance {-# OVERLAPPABLE #-} Subset s t => Subset s (x ': t) where
   subset (Ext _ xs) = subset xs

instance {-# OVERLAPS #-} Subset s t => Subset (x ': s) (x ': t) where
   subset (Ext x xs) = Ext x (subset xs)

{-| Splitting a union a set, given the sets we want to split it into -}
class Split s t st where
   -- where st ~ Union s t
   split :: Set st -> (Set s, Set t)

instance Split '[] '[] '[] where
   split Empty = (Empty, Empty)

instance {-# OVERLAPPABLE #-} Split s t st => Split (x ': s) (x ': t) (x ': st) where
   split (Ext x st) = let (s, t) = split st
                      in (Ext x s, Ext x t)

instance {-# OVERLAPS #-} Split s t st => Split (x ': s) t (x ': st) where
   split (Ext x st) = let (s, t) = split st
                      in  (Ext x s, t)

instance {-# OVERLAPS #-} (Split s t st) => Split s (x ': t) (x ': st) where
   split (Ext x st) = let (s, t) = split st
                      in  (s, Ext x t)

class Remove s t where
  remove :: Set s -> Proxy t -> Set (s :\ t)

instance Remove '[] t where
  remove Empty Proxy = Empty

instance {-# OVERLAPS #-} Remove xs x => Remove (x ': xs) x where
  remove (Ext _ xs) x@Proxy = remove xs x

instance {-# OVERLAPPABLE #-} (((y : xs) :\ x) ~ (y : (xs :\ x)), Remove xs x)
      => Remove (y ': xs) x where
  remove (Ext y xs) (x@Proxy) = Ext y (remove xs x)

{-| Value-level quick sort that respects the type-level ordering -}
class Sortable xs where
    quicksort :: Set xs -> Set (Sort xs)

instance Sortable '[] where
    quicksort Empty = Empty

instance (Sortable (Filter 'FMin p xs),
          Sortable (Filter 'FMax p xs), FilterV 'FMin p xs, FilterV 'FMax p xs) => Sortable (p ': xs) where
    quicksort (Ext p xs) = ((quicksort (less p xs)) `append` (Ext p Empty)) `append` (quicksort (more p xs))
                           where less = filterV (Proxy::(Proxy 'FMin))
                                 more = filterV (Proxy::(Proxy 'FMax))

type Unionable s t = (Sortable (s :++ t), Nubable (Sort (s :++ t)))

union :: (Unionable s t) => Set s -> Set t -> Set (UnionLists s t)
union s t = nub (quicksort (append s t))

{-| At the value level, noramlise the list form to the set form -}
asSet :: (Sortable s, Nubable (Sort s)) => Set s -> Set (AsSet s)
asSet x = nub (quicksort x)

{-| Useful properties to be able to refer to someties -}
type SetProperties (f :: [k]) =
  ( UnionLists f ('[] :: [k]) ~ f,
    Split f ('[] :: [k]) f,
    UnionLists ('[] :: [k]) f ~ f,
    Split ('[] :: [k]) f f,
    UnionLists f f ~ f,
    Split f f f,
    Unionable f ('[] :: [k]),
    Unionable ('[] :: [k]) f
  )
