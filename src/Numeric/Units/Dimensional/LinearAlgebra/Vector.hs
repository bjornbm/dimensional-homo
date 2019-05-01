{-
A representation of vectors where elements are quantities that may
have mixed physical dimensions. The goal is to check at compile
time that for any given operation the involved vectors have compatible
dimensions and that their elements have compatible physical dimensions.

One could argue that in most cases it makes little sense to have
quantities of different physical dimensions in any given vector/matrix,
and in general I agree. (Indeed, if we were to allow only "homogeneous"
vectors our (type-level) implementation could be much simplified.
Type-level HLists would not be necessary, only a single type parameter
for the physical dimension together with a 'PosType' for the length.)
However, linear algebra applications like kalman filtering and
weighted least squares estimation use heterogeneous state vectors
and covariance matrices.

In our initial implementation we use an inefficient internal
represenation of vectors based on plain lists. The idea is that
changing the internal representation to something more efficient
(e.g.  GSLHaskell) will be transparent once all the type trickery
has been worked out.

NOTE: This library allows construction of vectors and matrices with
no elements, e.g. using vTail. It could be argued that such vectors
and matrices should be disallowed, but the price would be more
complex type class instances. In practice, due to the static checking
for all operations I believe this is a non-issue and there is really
nothing dangerous or misleading one could do with the empty
vectors/matrices.
-}

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}

module Numeric.Units.Dimensional.LinearAlgebra.Vector
  {- ( Vec
  , vEmpty, vHead, vTail, vCons
  , fromHList, toHList
  ) -} where



import Data.Foldable as F hiding (sum)

import Data.AEq
import Data.Functor.Identity
import Data.Kind
import Data.List (intercalate, genericIndex, genericLength, genericTake)
import Data.Proxy
import Numeric.NumType.DK.Integers (TypeInt (Neg1, Pos2))
import GHC.TypeLits hiding (type (*))
import Numeric.Units.Dimensional.Prelude
import Numeric.Units.Dimensional -- (Dimensional (..), Quantity, Mul)
import Numeric.Units.Dimensional.Coercion
import qualified Orthogonals as O
import qualified Prelude as P


-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import qualified Data.AEq
-- >>> import Numeric.Units.Dimensional.LinearAlgebra
-- >>> let coerceD = coerce :: Quantity d a -> a
-- >>> let (~==) = (\x y -> coerceD x Data.AEq.~== coerceD y) :: Data.AEq.AEq a => Quantity d a -> Quantity d a -> Bool


-- Vector data type
-- ================

-- | A vector representation based on regular lists. The intent is that
-- the @ds@ type variable should be an HList of physical dimensions
-- corresponding to the elements of the list @[a]@. This will be an
-- abstract data type with constructor functions guaranteeing this
-- invariant.
newtype Vec (d :: Dimension) (n :: Nat) a = ListVec [a] deriving (Eq, AEq)

-- | `Elems` is a wrapper to provide Functor/Foldable/Traversable
  -- instances for vector.
  -- TODO `Elems` should be abstract and the only exposed interface (other than
  -- the instances) should be `toV` and `fromV`.
newtype Elems (n::Nat) q = Elems [q] deriving (Eq, AEq)

toElems :: Vec d n a -> Elems n (Quantity d a)
toElems = coerce

fromElems :: Elems n (Quantity d a) -> Vec d n a
fromElems = coerce

-- Derive automatically? TODO Write tests first?
instance Foldable (Elems n) where
  toList (Elems xs) = xs
  foldr f x0 = foldr f x0 . F.toList

-- Derive automatically? TODO Write tests first?
instance Functor (Elems n) where
  fmap f = Elems . fmap f . toList

-- Derive automatically? TODO Write tests first?
instance Traversable (Elems n) where
  traverse f = fmap Elems . traverse f . toList


-- | Convert a Vec to a list.
listElems :: Vec d n a -> [Quantity d a]
listElems = toList . toElems


-- Showing
-- -------
-- We implement a custom @Show@ instance.

instance (KnownDimension d, Show (Quantity d a), Num a) => Show (Vec d n a)
  where show = (\s -> "< " ++ s ++ " >")
             . intercalate ", "
             . map show
             . listElems

{-
Vector Construction and Deconstruction
======================================
Vectors can be primitively constructed using 'vCons' and 'vSing' and
deconstructed using 'vHead' and 'vTail'. We also provide type classes
for converting to/from HLists and tuples.
-}

-- | Create a singleton vector.
vSing :: Quantity d a -> Vec d 1 a
vSing = ListVec . pure . coerce

-- | Prepend an element to the vector.
vCons :: Quantity d a -> Vec d n a -> Vec d (n+1) a
vCons x (ListVec xs) = ListVec (coerce x:xs)

-- | Return the first element of the vector.
vHead :: (1 <= n) => Vec d n a -> Quantity d a
vHead (ListVec xs) = coerce $ head xs

-- | Drop the first element of the vector.
vTail :: (1 <= n) => Vec d (n + 1) a -> Vec d n a  -- Can create empty vector.
vTail (ListVec xs) = ListVec (tail xs)  -- vTransformUnsafe tail

-- TODO snoc and last?


-- -- Iteration
-- -- ---------
-- -- | Iterate a function over the elements of a vector. This can
-- -- be considered a form of uncurrying so the function operates
-- -- on a vector.
-- class VIterate d n a f -- b | d n a f -> b
--   where
--     type B d n a f :: *
--     vIterate :: (Quantity d a -> f) -> Vec d n a -> B d n a f
--
--
-- instance VIterate d 1 a b where
--   type B d 1 a b = b
--   vIterate f = f . vHead
--
-- instance VIterate d 1 a b => VIterate d 2 a (Quantity d a -> b) where
--   type B d 2 a (Quantity d a -> b) = B d 1 a b
--   vIterate g v = g (vHead v) `vIterate` vTail v


-- instance VIterate d 1 a f b => VIterate d 2 a (Quantity d a -> f) b
--   where vIterate g v = g (vHead v) `vIterate` vTail v
-- instance VIterate d 2 a f b => VIterate d 3 a (Quantity d a -> f) b
--   where vIterate g v = g (vHead v) `vIterate` vTail v
-- instance VIterate d 3 a f b => VIterate d 4 a (Quantity d a -> f) b
--   where vIterate g v = g (vHead v) `vIterate` vTail v

-- Convert to/from Tuples
-- ----------------------
-- | Convert to/from tuple representation. This is primarily to allow taking
-- advantage of the syntactic sugar tuples enjoy.

-- |
--
-- prop> \x y -> fromTuple (x *~ meter, y *~ kilo meter) == x *~ meter <:. y *~ kilo meter
-- prop> \(x::Double) (y::Double) -> let t = (x *~ meter, y *~ kilo meter) in toTuple (fromTuple t) == t
-- prop> \(x::Double) (y::Double) (z::Double) -> let t = (x *~ meter, y *~ kilo meter, z *~ centi meter) in toTuple (fromTuple t) == t
class FromTupleC t where
  type FromTuple t :: Type
  fromTuple :: t -> FromTuple t

instance FromTupleC (Quantity d a, Quantity d a) where
  type FromTuple (Quantity d a, Quantity d a) = Vec d 2 a
  fromTuple (x,y) = vCons x $ vSing y

instance FromTupleC (Quantity d a, Quantity d a, Quantity d a) where
  type FromTuple (Quantity d a, Quantity d a, Quantity d a) = Vec d 3 a
  fromTuple (x,y,z) = vCons x $ vCons y $ vSing z

class ToTupleC d n a where
  type ToTuple d n a :: Type
  toTuple :: Vec d n a -> ToTuple d n a

{-
We can brute force the instances out to a reasonable degree. Presumably
syntactic sugar loses its value if the vectors get to large as it is
impractical to deal with them any way other than programmatically.
-}

instance ToTupleC d 2 a where
  type ToTuple d 2 a = (Quantity d a, Quantity d a)
  toTuple v = (vElemAt n0 v, vElemAt n1 v)

instance ToTupleC d 3 a where
  type ToTuple d 3 a = (Quantity d a, Quantity d a, Quantity d a)
  toTuple v = (vElemAt n0 v, vElemAt n1 v, vElemAt n2 v)

n0 = Proxy :: Proxy 0
n1 = Proxy :: Proxy 1
n2 = Proxy :: Proxy 2

-- Querying
-- ========
-- | @vElem n vec@ returns the @n@:th element of @vec@. The index @n@
-- is zero-based. I could chose use an @HNat@ for indexing instead
-- of a @NumType@. It would simplify the type signatures but users of
-- dimensional are more likely to already have NumTypes in scope than
-- @HNat@s.
vElemAt :: (KnownNat m, m + 1 <= n) => Proxy m -> Vec d n a -> Quantity d a
vElemAt n = flip genericIndex (natVal n) . listElems


-- List conversions
-- ================

-- -- | Convert a Vec to a list.
-- toList :: Vec d n a -> [Quantity d a]
-- toList = coerce

-- | Create a Vec from a list. There is no guarantee that the list will
--   have the statically expected length, and an incorrect list length
--   is likely to cause difficult to debug problems down the line. To
--   catch incorrect list lengths early use `fromList` or `fromListError`
--   instead. (The only benefit of `fromListUnsafe` is better performance
--   than `fromListError` due to the absence of sanity checking.)
fromListUnsafe :: [Quantity d a] -> Vec d n a
fromListUnsafe = coerce

-- | Creata a Vec from a list. If the list is shorter than the expected
--   length it will be padded with the provided value. If the list is
--   longer than the expected length the list will be truncated.
--
-- >>> let x = 1 *~ meter
-- >>> fromListPad x [] `asTypeOf` (x <:. x)
-- < 1 m, 1 m >
fromListPad :: forall d n a . KnownNat n
            => Quantity d a -> [Quantity d a] -> Vec d n a
fromListPad x xs = fromListUnsafe $ genericTake n $ xs ++ repeat x
  where
    n = natVal (Proxy :: Proxy n)

-- | Creata a Vec from a list. If the list is shorter than the expected
--   length it will be padded with zeros. If the list is longer than the
--   expected length the list will be truncated.
--
-- >>> let x = 1 *~ meter
-- >>> fromListZero [x] `asTypeOf` vSing x
-- < 1 m >
-- >>> fromListZero [x,x] `asTypeOf` (x <:. x)
-- < 1 m, 1 m >
-- >>> fromListZero [x] `asTypeOf` (x <:. x)
-- < 1 m, 0 m >
-- >>> fromListZero [x,x] `asTypeOf` vSing x
-- < 1 m >
-- >>> fromListZero [] `asTypeOf` (x <:. x)
-- < 0 m, 0 m >
fromListZero :: (KnownNat n, Num a) => [Quantity d a] -> Vec d n a
fromListZero = fromListPad _0

-- | Creata a Vec from a list in a monad (for example @Maybe@). Fails if
--   the list is not of the expected length.
-- >>> let x = 1 *~ meter
-- >>> fromListM [x] `asTypeOf` Just (vSing x)
-- Just < 1 m >
-- >>> fromListM [x,x] `asTypeOf` Just (x <:. x)
-- Just < 1 m, 1 m >
-- >>> fromListM [x] `asTypeOf` Just (x  <:. x)
-- Nothing
-- >>> fromListM [x,x] `asTypeOf` Just (vSing x)
-- Nothing
fromListM :: forall d n a m . (Monad m, KnownNat n)
          => [Quantity d a] -> m (Vec d n a)
fromListM xs | len == n  = return $ fromListUnsafe xs
             | otherwise = fail msg
  where
    n   = natVal (Proxy :: Proxy n)
    len = genericLength xs
    msg = "List length (" ++ show len ++
          ") does not equal expected vector size (" ++ show n ++ ")"

-- | Creata a Vec from a list. Throws an exception if the list not of the
--   expected length.
--
-- >>> let x = 1 *~ meter
-- >>> fromListErr [x] `asTypeOf` vSing x
-- < 1 m >
-- >>> fromListErr [x,x] `asTypeOf` (x  <:. x)
-- < 1 m, 1 m >
-- >>> fromListErr [x] `asTypeOf` (x  <:. x)
-- < *** Exception: List length (1) does not equal expected vector size (2)
-- >>> fromListErr [x,x] `asTypeOf` vSing x
-- < *** Exception: List length (2) does not equal expected vector size (1)
fromListErr :: forall d n a m . (KnownNat n) => [Quantity d a] -> Vec d n a
fromListErr = runIdentity . fromListM


-- Utility functions
-- =================

-- | Map a function to the elements
mapElems :: (Quantity d1 a1 -> Quantity d2 a2) -> Vec d1 n a1 -> Vec d2 n a2
mapElems f = fromElems . fmap f . toElems

-- | Map a function to the elements
forElems :: Vec d1 n a1 -> (Quantity d1 a1 -> Quantity d2 a2) -> Vec d2 n a2
forElems = flip mapElems

-- | Zip the elements of two vectors using the provided function.
zipVecsWith :: (Quantity d1 a1 -> Quantity d2 a2 -> Quantity d3 a3)
            -> Vec d1 n a1 -> Vec d2 n a2 -> Vec d3 n a3
zipVecsWith f v1 v2 = fromListUnsafe $ zipWith f (listElems v1) (listElems v2)


-- Elementwise binary operators
-- ============================

-- | Elementwise addition of vectors. The vectors must have the
--   same size and element types.
elemAdd :: Num a => Vec d n a -> Vec d n a -> Vec d n a
elemAdd = zipVecsWith (+)

-- | Elementwise subraction of vectors. The vectors must have the
--   same size and element types.
elemSub :: Num a => Vec d n a -> Vec d n a -> Vec d n a
elemSub = zipVecsWith (-)


-- | Elementwise multiplication of vectors.
--   Multiplies each element i of the first argument vector by the
--   corresponding element of the second argument.
elemMul :: Num a => Vec d1 n a -> Vec d2 n a -> Vec ((*) d1 d2) n a
elemMul = zipVecsWith (*)


-- | Elementwise division of vectors
--   Divides each element i of the first argument vector by the
--   corresponding element of the second argument.
elemDiv :: Fractional a => Vec d1 n a -> Vec d2 n a -> Vec (d1 / d2) n a
elemDiv = zipVecsWith (/)


-- Scaling of vectors
-- ==================

-- | Scale a vector by multiplication. Each element of the vector is
--   multiplied by the first argument.
--
-- >>> let v1 = 4 *~ meter <:. 2 *~ meter
-- >>> let y  = 2 *~ second
-- >>> let v2 = 8 *~ (meter*second) <:. 4 *~ (meter*second)
-- >>> scaleVec y v1 == v2
-- True
scaleVec :: Num a => Quantity d1 a -> Vec d2 n a -> Vec ((*) d1 d2) n a
scaleVec = mapElems . (*)

-- | Scale a vector by division. Each element of the vector is
--   divided by the second argument.
--
-- >>> let v1 = 4 *~ meter <:. 2 *~ meter
-- >>> let y  = 2 *~ second
-- >>> let v2 = 2 *~ (meter/second) <:. 1 *~ (meter/second)
-- >>> scaleVecInv v1 y == v2
-- True
scaleVecInv :: Fractional a => Vec d1 n a -> Quantity d2 a -> Vec ((/) d1 d2) n a
scaleVecInv v = forElems v . flip (/)


-- TODO Check if used and useful?
-- -- | Scale a vector by a dimensionless quantity. This avoids inflating
-- --   the types for this common case.
-- scaleVec1 :: Num a => Dimensionless a -> Vec d n a -> Vec d n a
-- scaleVec1 x = vMap (x *)


-- Dot product
-- ===========
-- | Compute the dot product of two vectors.
--
-- >>> let x1 = 1 *~ meter;  x2 = 2 *~ meter;  v1 = x1 <:. x2
-- >>> let y1 = 3 *~ second; y2 = 4 *~ second; v2 = y1 <:. y2
-- >>> dotProduct v1 v2 == x1 * y1 + x2 * y2
-- True
dotProduct :: (Num a) => Vec d1 n a -> Vec d2 n a -> Quantity ((*) d1 d2) a
dotProduct v1 v2 = sumElems $ zipVecsWith (*) v1 v2


-- Cross product
-- =============
-- | Compute the (three element) cross product of two vectors.
--
-- >>> let v = 5 *~ meter <: 1 *~ meter <:. 2 *~ meter
-- >>> crossProduct v v == ListVec [0,0,0]
-- True
--
-- >>> :{
--   let
--     v1 =  1 *~ meter <: _0           <:. _0
--     v2 = _0          <:  1 *~ second <:. _0
--     v3 = _0          <: _0           <:.  1 *~ (meter * second)
--   in crossProduct v1 v2 == v3
-- :}
-- True
crossProduct :: Num a => Vec d1 3 a -> Vec d2 3 a -> Vec ((*) d1 d2) 3 a
crossProduct (ListVec [a, b, c]) (ListVec [d, e, f]) = ListVec
  [ b P.* f P.- e P.* c
  , c P.* d P.- f P.* a
  , a P.* e P.- d P.* b
  ]


-- Miscellaneous
-- =============

-- | Compute the sum of all elements in a homogenous vector.
sumElems :: (Num a) => Vec d n a -> Quantity d a
sumElems = sum . listElems

-- | Compute the vector norm.
--
-- >>> let v = m <:. m where m = 1 *~ meter
-- >>> :set -XFlexibleContexts
-- >>> norm v == sqrt (v `dotProduct` v)
-- True
norm :: (RealFloat a) => Vec d n a -> Quantity d a
norm v = coerceSafe $ sqrt $ dotProduct v v  -- O.norm
  where
    --coerceSafe :: Quantity (Sqrt ((*) d d)) a -> Quantity d a  TODO next dimensional release
    coerceSafe :: Quantity (Sqrt ((*) d d)) a -> Quantity d a
    coerceSafe = coerce

-- | Normalize a vector. The vector must be homogeneous.
--
-- >>> let m = 3 *~ meter
-- >>> let v = m <:. m
-- >>> normalize v == (_1 / norm v) `scaleVec` v
-- True
-- >>> normalize v == (norm v ^ neg1) `scaleVec` v
-- True
-- >>> let m = 3 *~ meter in normalize (vSing m)
-- < 1.0 >
-- >>> norm (normalize v) ~== (1.0 *~ one)
-- True
normalize :: forall d n a . RealFloat a => Vec d n a -> Vec DOne n a
normalize v = scaleVecInv v (norm v)

-- | Negate a vector.
negateVec :: (Num a) => Vec d n a -> Vec d n a
negateVec = mapElems negate
