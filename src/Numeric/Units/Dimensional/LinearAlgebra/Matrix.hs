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

import Data.Foldable
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
-- through the API.
newtype Mat (d :: Dimension) (r :: Nat) (c:: Nat) a = ListMat [[a]] deriving Eq


-- Showing
-- -------
-- A custom @show@ instance for debugging purposes.
instance (KnownDimension d, Fractional a, Show a) => Show (Mat d n n a) where
  show = (\s -> "<< " ++ s ++ " >>")
       . intercalate " >,\n < "
       . map (intercalate ", ")
       . map (map show)
       . toRowLists


-- Matrix Construction and Deconstruction
-- ======================================

-- | Convert ("promote") a vector to a row matrix.
rowMatrix :: Vec d n a -> Mat d 1 n a
rowMatrix (ListVec xs) = ListMat [xs]

-- | Convert ("promote") a vector to a column matrix.
colMatrix :: Vec d n a -> Mat d n 1 a
colMatrix (ListVec xs) = ListMat (map pure xs)

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


-- Folding and traversing
-- ======================

-- Rows
-- ----
-- | Newtype for representing a matrix as a list of row vectors.
  --
  --  [ x11 x12 x13 ]      [ < x11 x12 x13>
  --  [ x21 x22 x23 ]  =>  , < x21 x22 x23>
  --  [ x31 x32 x33 ]      , < x31 x32 x33> ]
  --
newtype Rows (r :: Nat) v = Rows [v] deriving (Eq)

toRows :: Mat d r c a -> Rows r (Vec d c a)
toRows = coerce

fromRows :: Rows r (Vec d c a) -> Mat d r c a
fromRows = coerce

instance Foldable (Rows r) where
  toList = coerce
  foldr f x0 = foldr f x0 . toList

instance Functor (Rows r) where
  fmap f = Rows . fmap f . toList

instance Traversable (Rows r) where
  traverse f = fmap Rows . traverse f . toList


-- Columns
-- -------
-- | Newtype for representing a matrix as a list of column vectors.
  --
  --  [ x11 x12 x13 ]      [ < x11 x21 x31>
  --  [ x21 x22 x23 ]  =>  , < x12 x22 x32>
  --  [ x31 x32 x33 ]      , < x13 x22 x33> ]
  --
newtype Cols (c :: Nat) v = Cols [v] deriving (Eq)

toCols :: forall d r c a . Mat d r c a -> Cols c (Vec d c a)
toCols (ListMat rs) = coerce $ O.transposed rs

fromCols :: forall d r c a . Cols c (Vec d c a) -> Mat d r c a
fromCols cs = coerce $ O.transposed (coerce cs :: [[a]])

instance Foldable (Cols c) where
  toList = coerce
  foldr f x0 = foldr f x0 . toList

instance Functor (Cols c) where
  fmap f = Cols . fmap f . toList

instance Traversable (Cols c) where
  traverse f = fmap Cols . traverse f . toList


-- Elements by row then column
-- ---------------------------
-- | Newtype for representing a matrix as a list elements, with rows
  -- having greater cardinality than columns.
  --
  --  [ x11 x12 x13 ]      [ x11 , x12 , x13
  --  [ x21 x22 x23 ]  =>  , x21 , x22 , x23
  --  [ x31 x32 x33 ]      , x31 , x32 , x33> ]
  --
newtype RowsCols (r :: Nat) (c :: Nat) q = RowsCols [[q]] deriving (Eq)

toRowsCols :: forall d r c a . Mat d r c a -> RowsCols r c (Quantity d a)
toRowsCols = RowsCols . map listElems . toList . toRows

fromRowsCols :: forall d r c a . RowsCols r c (Quantity d a) -> Mat d r c a
fromRowsCols = fromRows . coerce

instance Foldable (RowsCols r c) where
  toList = concat . (coerce :: RowsCols r c q -> [[q]])
  foldr f x0 = foldr f x0 . toList

instance Functor (RowsCols r c) where
  fmap f (RowsCols rs)= RowsCols $ fmap (fmap f) rs

instance Traversable (RowsCols r c) where
  traverse f (RowsCols rs) = fmap RowsCols $ traverse (traverse f) rs


-- Elements by column then row
-- ---------------------------
-- | Newtype for representing a matrix as a list elements, with columns
  -- having greater cardinality than rows.
  --
  --  [ x11 x12 x13 ]      [ x11 , x21 , x31
  --  [ x21 x22 x23 ]  =>  , x12 , x22 , x32
  --  [ x31 x32 x33 ]      , x13 , x22 , x33 ]
  --
newtype ColsRows (r :: Nat) (c :: Nat) q = ColsRows [[q]] deriving (Eq)

toColsRows :: forall d r c a . Mat d r c a -> ColsRows r c (Quantity d a)
toColsRows = ColsRows . map listElems . toList . toCols

fromColsRows :: forall d r c a . ColsRows r c (Quantity d a) -> Mat d r c a
fromColsRows = fromCols . coerce

instance Foldable (ColsRows r c) where
  toList = concat . (coerce :: ColsRows r c q -> [[q]])
  foldr f x0 = foldr f x0 . toList

instance Functor (ColsRows r c) where
  fmap f (ColsRows rs)= ColsRows $ fmap (fmap f) rs

instance Traversable (ColsRows r c) where
  traverse f (ColsRows rs) = fmap ColsRows $ traverse (traverse f) rs


toRowVecs :: Mat d r c a -> [Vec d c a]
toRowVecs = toList . toRows
toColVecs :: Mat d r c a -> [Vec d c a]
toColVecs = toList . toCols
toRowLists :: Mat d r c a -> [[Quantity d a]]
toRowLists = map listElems . toRowVecs
toColLists :: Mat d r c a -> [[Quantity d a]]
toColLists = map listElems . toColVecs


-- Transpose
-- =========
-- | Transpose a matrix.
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


-- Miscellaneous
-- =============

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
-- type.
identity :: forall d n a . (KnownNat n, Num a) => Mat d n n a
identity = ListMat $ O.unit_matrix $ fromInteger $ natVal (Proxy :: Proxy n)
