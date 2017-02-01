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

module Numeric.Units.Dimensional.LinearAlgebra.Vector
  {- ( Vec
  , vEmpty, vHead, vTail, vCons
  , fromHList, toHList
  ) -} where




import Data.Functor.Identity
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
-- >>> let coerceD = coerce :: Quantity d a -> a
-- >>> let (~==) = (\x y -> coerceD x Data.AEq.~== coerceD y) :: Data.AEq.AEq a => Quantity d a -> Quantity d a -> Bool


-- Vector data type
-- ================

-- | A vector representation based on regular lists. The intent is that
-- the @ds@ type variable should be an HList of physical dimensions
-- corresponding to the elements of the list @[a]@. This will be an
-- abstract data type with constructor functions guaranteeing this
-- invariant.
newtype Vec (d :: Dimension) (n :: Nat) a = ListVec [a] deriving (Eq)


-- Showing
-- -------
-- We implement a custom @Show@ instance.

instance (KnownDimension d, Show (Quantity d a), Num a) => Show (Vec d n a)
  where show = (\s -> "< " ++ s ++ " >")
             . intercalate ", "
             . map show
             . toList

{-
Vector Construction and Deconstruction
======================================
Vectors can be primitively constructed using 'vCons' and 'vSing' and
deconstructed using 'vHead' and 'vTail'. We also provide type classes
for converting to/from HLists and tuples.
-}

-- | Create a singleton vector.
vSing :: Quantity d a -> Vec d 1 a
-- vSing x = ListVec [x /~ siUnit]
vSing x = coerce [x]

-- | Prepend an element to the vector.
vCons :: Quantity d a -> Vec d n a -> Vec d (n+1) a
vCons x (ListVec xs) = ListVec (coerce x:xs)

-- | Return the first element of the vector.
vHead :: Vec d (n+1) a -> Quantity d a
vHead (ListVec xs) = coerce $ head xs

-- | Drop the first element of the vector.
vTail :: Vec d n a -> Vec d (n-1) a  -- Can create empty vector.
vTail (ListVec xs) = ListVec (tail xs)  -- vTransformUnsafe tail


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
-- prop> \x y -> fromTuple (x *~ meter, y *~ kilo meter) == vCons (x *~ meter) (vSing (y *~ kilo meter))
-- prop> \(x::Double) (y::Double) -> let t = (x *~ meter, y *~ kilo meter) in toTuple (fromTuple t) == t
-- prop> \(x::Double) (y::Double) (z::Double) -> let t = (x *~ meter, y *~ kilo meter, z *~ centi meter) in toTuple (fromTuple t) == t
class FromTuple t where
  type V t :: *
  fromTuple :: t -> V t

instance FromTuple (Quantity d a, Quantity d a) where
  type V (Quantity d a, Quantity d a) = Vec d 2 a
  fromTuple (x,y) = vCons x $ vSing y

instance FromTuple (Quantity d a, Quantity d a, Quantity d a) where
  type V (Quantity d a, Quantity d a, Quantity d a) = Vec d 3 a
  fromTuple (x,y,z) = vCons x $ vCons y $ vSing z

class ToTuple d n a where
  type T d n a :: *
  toTuple :: Vec d n a -> T d n a

instance ToTuple d 2 a where
  type T d 2 a = (Quantity d a, Quantity d a)
  toTuple v = (vElemAt n0 v, vElemAt n1 v)

instance ToTuple d 3 a where
  type T d 3 a = (Quantity d a, Quantity d a, Quantity d a)
  toTuple v = (vElemAt n0 v, vElemAt n1 v, vElemAt n2 v)



-- class ToTuple v where
--   type T v :: *
--   toTuple   :: v -> T v
--
-- class FromTuple t where
--   type V t :: *
--   fromTuple :: t -> V t
--
-- instance ToTuple (Vec d 2 a) where
--   type T (Vec d 2 a) = (Quantity d a, Quantity d a)
--   toTuple v = (vElemAt n0 v, vElemAt n1 v)
--
-- instance FromTuple (Quantity d a, Quantity d a) where
--   type V (Quantity d a, Quantity d a) = Vec d 2 a
--   fromTuple (x,y) = vCons x $ vSing y

-- instance ToTuple (Vec d 3 a) where
--   type T (Vec d 3 a) = (Quantity d a, Quantity d a, Quantity d a)
--   toTuple v = (vElemAt n0 v, vElemAt n1 v, vElemAt n2 v)
--
-- instance FromTuple (Quantity d a, Quantity d a, Quantity d a) where
--   type V (Quantity d a, Quantity d a, Quantity d a) = Vec d 3 a
--   fromTuple (x,y,z) = vCons x $ vCons y $ vSing z


{-
We can brute force the instances out to a reasonable degree. Presumably
syntactic sugar loses its value if the vectors get to large as it is
impractical to deal with them any way other than programmatically.
-}

-- -- |
-- --
-- -- prop> \x y -> fromTuple (x *~ meter, y *~ kilo meter) == vCons (x *~ meter) (vSing (y *~ kilo meter))
-- -- prop> \(x::Double) (y::Double) -> let t = (x *~ meter, y *~ kilo meter) in toTuple (fromTuple t) == t
-- instance VTuple (Vec d 2 a) (Quantity d a, Quantity d a) where
--   toTuple v = (vElemAt n0 v, vElemAt n1 v)
--   -- toTuple = vIterate (,)
--   fromTuple (x,y) = vCons x $ vSing y

-- |
--
-- -- prop> \(x::Double) (y::Double) (z::Double) -> let t = (x *~ meter, y *~ kilo meter, z *~ centi meter) in toTuple (fromTuple t) == t
-- instance VTuple (Vec d 3 a)
--                 (Quantity d a, Quantity d a, Quantity d  a) where
--   toTuple v = (vElemAt n0 v, vElemAt n1 v, vElemAt n2 v)
--   -- toTuple = vIterate (,,)
--   fromTuple (x,y,z) = vCons x $ vCons y $ vSing z

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
vElemAt n = flip genericIndex (natVal n) . toList


-- -- Homogenity
-- -- ==========
-- -- | This class guarantees that a vector is homogenuous w r t the
-- -- physical dimensions of its element.
-- class Homo ds d | ds -> d where
--   -- | Converts a homogeneous vector to a list.
--   toList :: Vec ds a -> [Quantity d a]
--   toList (ListVec xs) = map Dimensional xs
-- instance Homo (HSing d) d
-- instance Homo (d:*:ds) d => Homo (d:*:(d:*:ds)) d


-- List conversions
-- ================

-- | Convert a Vec to a list.
toList :: Vec d n a -> [Quantity d a]
toList = coerce

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
-- >>> fromListPad x [] `asTypeOf` vCons x (vSing x)
-- < 1.0 m, 1.0 m >
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
-- < 1.0 m >
-- >>> fromListZero [x,x] `asTypeOf` vCons x (vSing x)
-- < 1.0 m, 1.0 m >
-- >>> fromListZero [x] `asTypeOf` vCons x (vSing x)
-- < 1.0 m, 0.0 m >
-- >>> fromListZero [x,x] `asTypeOf` vSing x
-- < 1.0 m >
-- >>> fromListZero [] `asTypeOf` vCons x (vSing x)
-- < 0.0 m, 0.0 m >
fromListZero :: (KnownNat n, Num a) => [Quantity d a] -> Vec d n a
fromListZero = fromListPad _0

-- | Creata a Vec from a list in a monad (for example @Maybe@). Fails if
--   the list is not of the expected length.
-- >>> let x = 1 *~ meter
-- >>> fromListM [x] `asTypeOf` Just (vSing x)
-- Just < 1.0 m >
-- >>> fromListM [x,x] `asTypeOf` Just (vCons x (vSing x))
-- Just < 1.0 m, 1.0 m >
-- >>> fromListM [x] `asTypeOf` Just (vCons x (vSing x))
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
-- < 1.0 m >
-- >>> fromListErr [x,x] `asTypeOf` vCons x (vSing x)
-- < 1.0 m, 1.0 m >
-- >>> fromListErr [x] `asTypeOf` vCons x (vSing x)
-- < *** Exception: List length (1) does not equal expected vector size (2)
-- >>> fromListErr [x,x] `asTypeOf` vSing x
-- < *** Exception: List length (2) does not equal expected vector size (1)
fromListErr :: forall d n a m . (KnownNat n) => [Quantity d a] -> Vec d n a
fromListErr = runIdentity . fromListM


{-
Utility functions (TODO update docs?)
=====================================
Note that the type signatures permit coercion. The burden of verifying
consistency with type signature rests on user. Care must be taken
to specify expected/desired return type explicitly to be sure
expected results are obtained. These functions should not be exported
outside this module!
-}


-- | Map a function to the elements
vMap :: (Quantity d1 a1 -> Quantity d2 a2) -> Vec d1 n a1 -> Vec d2 n a2
vMap f = fromListUnsafe . map f . toList

-- | Zip the numeric representation of the elements using the provided
-- function. IMPORTANT: v1 v2 v3 must have the same length!
vZipWith :: (Quantity d1 a1 -> Quantity d2 a2 -> Quantity d3 a3)
         -> Vec d1 n a1 -> Vec d2 n a2 -> Vec d3 n a3
vZipWith f v1 v2 = fromListUnsafe $ zipWith f (toList v1) (toList v2)


-- Elementwise binary operators
-- ============================

-- | Elementwise addition of vectors. The vectors must have the
--   same size and element types.
elemAdd :: Num a => Vec d n a -> Vec d n a -> Vec d n a
elemAdd = vZipWith (+)

-- | Elementwise subraction of vectors. The vectors must have the
--   same size and element types.
elemSub :: Num a => Vec d n a -> Vec d n a -> Vec d n a
elemSub = vZipWith (-)


-- | Elementwise multiplication of vectors.
--   Multiplies each element i of the first argument vector by the
--   corresponding element of the second argument.
elemMul :: Num a => Vec d1 n a -> Vec d2 n a -> Vec ((*) d1 d2) n a
elemMul = vZipWith (*)


-- | Elementwise division of vectors
--   Divides each element i of the first argument vector by the
--   corresponding element of the second argument.
elemDiv :: Fractional a => Vec d1 n a -> Vec d2 n a -> Vec (d1 / d2) n a
elemDiv = vZipWith (/)


-- Scaling of vectors
-- ==================

-- | Scale a vector by multiplication. Each element of the vector is
--   multiplied by the first argument.
scaleVec :: Num a => Quantity d1 a -> Vec d2 n a -> Vec ((*) d1 d2) n a
scaleVec x = vMap (x *)

-- | Scale a vector by division. Each element of the vector is
--   divided by the second argument.
scaleVecInv :: Fractional a => Vec d1 n a -> Quantity d2 a -> Vec ((/) d1 d2) n a
scaleVecInv v x = vMap (/ x) v


-- TODO Check if used and useful?
-- -- | Scale a vector by a dimensionless quantity. This avoids inflating
-- --   the types for this common case.
-- scaleVec1 :: Num a => Dimensionless a -> Vec d n a -> Vec d n a
-- scaleVec1 x = vMap (x *)


-- Dot product
-- ===========
-- | Compute the dot product of two vectors.
--
-- >>> let x1 = 1 *~ meter;  x2 = 2 *~ meter;  v1 = vCons x1 (vSing x2)
-- >>> let y1 = 3 *~ second; y2 = 4 *~ second; v2 = vCons y1 (vSing y2)
-- >>> dotProduct v1 v2 == x1 * y1 + x2 * y2
-- True
dotProduct :: (Num a) => Vec d1 n a -> Vec d2 n a -> Quantity ((*) d1 d2) a
dotProduct v1 v2 = vSum $ vZipWith (*) v1 v2

{-
Cross product
=============
Vector cross product is only applicable to vectors with three
elements (I believe). The constraints for the instance are brute-force.
It is slightly disconcerting that nothing prevents defining additional
nstances...
-}

-- | Compute the cross product of two vectors.
--
-- >>> let x1 = 1 *~ meter; x2 = 2 *~ meter; v1 = vCons x2 (vCons x1 (vSing x2))
-- >>> crossProduct v1 v1 == ListVec [0,0,0]
-- True
--
-- >>> let x = 1 *~ meter;  v1 = vCons x  (vCons _0 (vSing _0))
-- >>> let y = 1 *~ second; v2 = vCons _0 (vCons y  (vSing _0))
-- >>> let z = 1 *~ (meter * second); v3 = vCons _0 (vCons _0  (vSing z))
-- >>> crossProduct v1 v2 == v3
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
vSum :: (Num a) => Vec d n a -> Quantity d a
vSum = sum . toList

-- coerceQ :: (KnownDimension d1, KnownDimension d2, Fractional a) => Quantity d1 a -> Quantity d2 a
-- coerceQ x = (x /~ siUnit) *~ siUnit
-- coerceV :: Vec d1 n a -> Vec d2 n a
-- coerceV (ListVec xs) = ListVec xs

-- | Compute the vector norm.
--
-- >>> let m = 1 *~ meter
-- >>> let v = vCons m (vSing m)
-- >>> :set -XFlexibleContexts
-- >>> vNorm v == sqrt (v `dotProduct` v)
-- True
vNorm :: (RealFloat a) => Vec d n a -> Quantity d a
vNorm v = coerceSafe $ sqrt $ dotProduct v v  -- O.norm
  where
    --coerceSafe :: Quantity (Sqrt ((*) d d)) a -> Quantity d a  TODO next dimensional release
    coerceSafe :: Quantity (Root ((*) d d) Pos2) a -> Quantity d a
    coerceSafe = coerce

-- | Normalize a vector. The vector must be homogeneous.
--
-- >>> let m = 1 *~ meter
-- >>> let v = vCons m (vSing m)
-- >>> vNormalize v == (_1 / vNorm v) `scaleVec` v
-- True
-- >>> vNormalize v == (vNorm v ^ neg1) `scaleVec` v
-- True
-- >>> let m = 1 *~ meter in vNormalize (vSing m)
-- < 1.0 >
-- >>> vNorm (vNormalize v) ~== (1.0 *~ one)
-- True
vNormalize :: forall d n a . RealFloat a => Vec d n a -> Vec DOne n a
vNormalize v = scaleVecInv v (vNorm v)
-- vNormalize v =  coerceSafe $ (_1 / vNorm v) `scaleVec` v
--   where
--     coerceSafe :: Vec ((*) (DOne / d) d) n a -> Vec DOne n a
--     coerceSafe = coerce

-- | Negate a vector.
vNegate :: (Num a) => Vec d n a -> Vec d n a
vNegate = vMap negate
