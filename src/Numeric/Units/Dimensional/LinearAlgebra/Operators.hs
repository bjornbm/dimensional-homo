{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}

-- | Convention:
--
--   @>@  Vector to the left of operator (mnemonic: v)
--   @<@  Vector to the right of operator (mnemonic: v)
--   @|@  Matrix to side of operator
--   @.@  Last element of vector/matrix.
--
-- The above symbols were chosen to minimize risk of conflict with common
-- operators from other libraries (based on Hoogle search).

module Numeric.Units.Dimensional.LinearAlgebra.Operators where

import Data.Proxy
import GHC.TypeLits hiding (type (*))
import Numeric.Units.Dimensional.LinearAlgebra.Vector
import Numeric.Units.Dimensional.LinearAlgebra.Matrix
import Numeric.Units.Dimensional.Prelude
import qualified Prelude


-- Operator fixity analogous with Prelude.
infixl 9  >!!
infixl 7  *<, >*, >/, >.<, *|, |*, |*|, |*<, >*|
infixl 6  >+<, >-<, |+|, |-|
infixr 5  <:, <:., |:, |:.

-- These in these construction operators the @:@ cannot be to the left
-- so the order of characters in the operator are somewhat reversed from
-- the ideal we are forced to reverse order of characters from the ideal
-- (for consistency with other operator conventions in this module the
-- @>@ and @|@ should have been on the right side of the operator).

(<:) = vCons
x <:. y = x <: vSing y
(|:)  :: Vec d c a -> Mat d r c a -> Mat d (r+1) c a
(|:)  = consRow
v1 |:. v2 = v1 |: rowMatrix v2

-- | Vector element querying.
(>!!) :: (KnownNat m, m + 1 <= n) => Vec d n a -> Proxy m -> Quantity d a
v >!! n = vElemAt n v

-- Vectors
(>+<), (>-<) :: Num a => Vec d n a -> Vec d n a -> Vec d n a
(>+<) = elemAdd
(>-<) = elemSub
(*<)  :: Num a => Quantity d1 a -> Vec d2 n a -> Vec ((*) d1 d2) n a
(*<)  = scaleVec
(>*)  :: Num a => Vec d1 n a -> Quantity d2 a -> Vec ((*) d2 d1) n a
(>*)  = flip scaleVec
(>/)  :: Fractional a => Vec d1 n a -> Quantity d2 a -> Vec ((/) d1 d2) n a
(>/) = scaleVecInv
(>.<) :: Num a => Vec d1 n a -> Vec d2 n a -> Quantity ((*) d1 d2) a
(>.<) = dotProduct

-- Matrices
(|+|), (|-|) :: Num a => Mat d r c a -> Mat d r c a -> Mat d r c a
(|+|) = mElemAdd
(|-|) = mElemSub
(|*|) :: Num a => Mat d1 r n a -> Mat d2 n c a -> Mat ((*) d1 d2) r c a
(|*|) = matMat
(*|)  :: Num a => Quantity d1 a -> Mat d2 r c a -> Mat ((*) d1 d2) r c a
(*|)  = scaleMat
(|*)  :: Num a => Mat d1 r c a -> Quantity d2 a -> Mat ((*) d2 d1) r c a
(|*)  = flip scaleMat
(|*<) :: Num a => Mat d1 r c a -> Vec d2 c a -> Vec ((*) d1 d2) r a
(|*<) = matVec
(>*|) :: Num a => Vec d1 r a -> Mat d2 r c a -> Vec ((*) d2 d1) c a
(>*|) v m = transpose m |*< v   -- vecMat v m
