{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Numeric.Units.Dimensional.LinearAlgebra.Matrix where

import Data.List (intercalate)
import Data.Proxy
import GHC.TypeLits hiding (type (*))
import Numeric.Units.Dimensional.Prelude
import Numeric.Units.Dimensional (Dimensional (..))
import Numeric.Units.Dimensional.Coercion
import Numeric.Units.Dimensional.LinearAlgebra.Vector
import qualified Orthogonals as O
import qualified Prelude as P


-- | A matrix is a list of rows (which in turn are lists). The matrix construction
-- functions available (i.e. 'consRow') guarantee that matrices are well-formed
-- (each row has the same number of elements). That a matrix is a list of rows as
-- opposed to a list of columns is an implementation detail that we try to not leak
-- through the API. Ultimately, however, that choice will be visible through the
-- type signatures of matrices.
newtype Mat (d :: Dimension) (r :: Nat) (c:: Nat) a = ListMat [[a]] deriving Eq

toRowVecs :: Mat d r c a -> [Vec d r a]
toRowVecs = map fromListUnsafe . coerce
toRowLists = map toList . toRowVecs

-- Showing
-- -------
-- A custom @show@ instance for debugging purposes.

instance (KnownDimension d, Fractional a, Show a) => Show (Mat d n n a) where
  show = (\s -> "<< " ++ s ++ " >>")
       . intercalate " >,\n < "
       . map (intercalate ", ")
       . map (map show)
       . toRowLists


-- Rows and colums
-- ---------------

-- -- | Class constraining the number of rows in a matrix. No guarantees
-- -- are provided for wellformedness (i.e. all rows of equal length).
-- class Rows vs n | vs -> n
-- instance HLength vs n => Rows vs n  -- Trivial.
--
-- -- Class constraining the number of columns in a matrix. In particular
-- -- ensures that all matrix is well-formed (all colums are of equal
-- -- length).
-- class Cols vs n | vs -> n
-- instance (HLength v n) => Cols (HSing v) n
-- instance (HLength v n, Cols vs n) => Cols (v:*:vs) n
--
-- -- | Class ensuring a matrix is wellformed. A matrix is well-formed
-- -- if it has at least one non-empty row and all of its rows are of
-- -- equal length.
-- class Wellformed vs
-- instance Cols v (HSucc n) => Wellformed v
--
-- -- | Class constraining the shape of a matrix to a square.
-- class Square vs n | vs -> n
-- instance (Cols vs n, Rows vs n) => Square vs n


-- Matrix Construction and Deconstruction
-- ======================================

-- | Convert ("promote") a vector to a row matrix.
rowMatrix :: Vec d n a -> Mat d 1 n a
rowMatrix (ListVec xs) = ListMat [xs]

-- | Convert ("promote") a vector to a column matrix.
colMatrix :: Vec d n a -> Mat d n 1 a
colMatrix (ListVec xs) = ListMat (map (:[]) xs)

-- | Prepends a row to a matrix.
consRow :: Vec d n a -> Mat d r n a -> Mat d (r+1) n a
consRow (ListVec v) (ListMat vs) = ListMat (v:vs)

-- | Prepends a column to a matrix.
consCol :: Vec d n a -> Mat d n c a -> Mat d n (c+1) a
consCol (ListVec xs) (ListMat vs) = ListMat (zipWith (:) xs vs)


-- | Return the first row of the matrix.
rowHead :: Mat d r c a -> Vec d c a
rowHead (ListMat vs) = ListVec (head vs)

-- | Drop the first row of the matrix.
rowTail :: Mat d r c a -> Mat d (r-1) c a
rowTail (ListMat vs) = ListMat (tail vs)


-- Convert to/from HLists
-- ----------------------
-- | This class allows converting a matrix to an equivalent HList of
-- HLists (each representing one row in the matrix) or from a
-- well-formed HList of HLists into a matrix.
--
-- Properties:
--   fromRowHLists . toRowHLists = id
--   toRowHLists . fromRowHLists = id
--
-- class RowHLists m l | m -> l, l -> m where
--     toRowHLists   :: m -> l
--     fromRowHLists :: l -> m
--
-- instance VHList (Vec v a) l => RowHLists (Mat (HSing v) a) (HSing l) where  -- Can create empty matrix.
--     toRowHLists   m = HCons (toHList $ rowHead m) HNil
--     fromRowHLists (HCons l HNil) = rowMatrix $ fromHList l
--
-- instance (VHList (Vec v a) l, RowHLists (Mat vs a) ls, Wellformed (v:*:vs))
--       => RowHLists (Mat (v:*:vs) a) (l:*:ls)
--   where
--     toRowHLists m = HCons (toHList (rowHead m)) (toRowHLists (rowTail m))
--     fromRowHLists (HCons l ls) = consRow (fromHList l) (fromRowHLists ls)


-- Transpose
-- =========
-- Thanks to the @Apply ConsEach@ instances the 'Transpose' instance
-- is pretty simple!
--
-- Properties:
--   tranpose . transpose = id
--
transpose :: Mat d r c a -> Mat d c r a
transpose (ListMat vs) = ListMat (O.transposed vs)


-- Matrix times vector
-- ===================
-- | Multiplying a matrix by a vector. What is the fancy term... project??
matVec :: Num a => Mat d1 r c a -> Vec d2 c a -> Vec ((*) d1 d2) r a
matVec (ListMat vs) (ListVec v) = ListVec (O.matrix_ket vs v)

-- data DotProd
-- instance DotProduct v1 v2 v3 => Apply  DotProd (v2, v1) v3
--   where apply _ _ = undefined
-- instance DotProduct v1 v2 v3 => Apply (DotProd, v2) v1  v3
--   where apply _ _ = undefined
-- instance HMap (DotProd, v) m v' => MatrixVector m v v'

-- | Multiplying a vector to the left of a matrix. This is equivalent
-- to multiplying a vector to the right of the transposed matrix.
vecMat :: Num a => Vec d1 r a -> Mat d2 r c a -> Vec ((*) d2 d1) c a
vecMat v m = transpose m `matVec` v

-- | The dyadic product.
dyadicProduct :: Num a => Vec d1 r a -> Vec d2 c a -> Mat ((*) d1 d2) r c a
v1 `dyadicProduct` v2 = colMatrix v1 `matMat` rowMatrix v2


-- Matrix times matrix
-- ===================
-- | Multiplication of two matrices.
matMat :: Num a => Mat d1 r n a -> Mat d2 n c a -> Mat ((*) d1 d2) r c a
matMat (ListMat m) (ListMat m') = ListMat (O.matrix_matrix m (O.transposed m'))

-- data MatVec
-- instance MatrixVector m v v' => Apply  MatVec (m, v) v' where apply _ _ = undefined
-- instance MatrixVector m v v' => Apply (MatVec, m) v  v' where apply _ _ = undefined
-- instance (Transpose m2 m2', HMap (MatVec, m1) m2' m3', Transpose m3' m3)
--       => MatrixMatrix m1 m2 m3


-- Miscellaneous
-- =============
-- Scale a matrix (multiply by a scalar).

-- data ScaleV
-- instance HMap (MulD, d) ds1 ds2 => Apply  ScaleV (d, ds1) ds2 where apply _ = undefined
-- instance HMap (MulD, d) ds1 ds2 => Apply (ScaleV, d) ds1  ds2 where apply _ = undefined

-- | Scale a matrix (multiply by a scalar).
scaleMat :: (Num a) => Quantity d1 a -> Mat d2 r c a -> Mat ((*) d1 d2) r c a
scaleMat x = coerce . map (scaleVec x) . toRowVecs

-- Addition and subtraction of matrices.

-- | Elementwise addition of matrices.
mElemAdd :: Num a => Mat d r c a -> Mat d r c a -> Mat d r c a
mElemAdd (ListMat vs1) (ListMat vs2) = ListMat (zipWith (zipWith (P.+)) vs1 vs2)

-- | Elementwise subtraction of matrices.
mElemSub :: Num a => Mat d r c a -> Mat d r c a -> Mat d r c a
mElemSub (ListMat vs1) (ListMat vs2) = ListMat (zipWith (zipWith (P.-)) vs1 vs2)

-- | The identity matrix. The size of the matrix is determined by its
-- type. The physical dimensions of the elements of the identity
-- matrix necessarily depend on the matrix or vector it will operate on
-- (by multiplication). Not all matrices have a valid identity matrix,
-- but when an identity matrix exists the elements on the diagonal are
-- always dimensionless. Unfortunately this function does not assist
-- in determining the type of the identity matrix, but when it is
-- involved in addition or subtraction it can be inferred.
identity :: forall d n a . (KnownNat n, Num a) => Mat d n n a
identity = ListMat $ O.unit_matrix $ fromInteger $ natVal (Proxy :: Proxy n)


-- -- Homogeneous Matrices
-- -- ====================
-- -- | Class constraining to homogeneous matrices. A matrix is
-- -- homogeneous if all elements have the same physical dimensions.
-- class MHomo vs d | vs -> d
-- instance (Homo v d) => MHomo (HSing v) d
-- instance (Homo v d, MHomo vs d) => MHomo (v:*:vs) d
