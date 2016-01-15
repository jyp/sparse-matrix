{-# LANGUAGE DataKinds, KindSignatures, GADTs #-}

module Closure where

import Algebra.Classes
import Prelude (Bool(..),otherwise,Int,print)

class (Ring a, ZeroTest a) => RingZ a where

class ZeroTest a where
  isZero :: a -> Bool

data Shape = Bin Shape Shape | Leaf

data Shape' :: Shape -> * where
  Bin' :: !Int -> Shape' s -> Shape' s' -> Shape' ('Bin s s')
  Leaf' :: Shape' 'Leaf

data SomeShape where
  S :: Shape' s -> SomeShape

data Mat :: Shape -> Shape -> * -> * where
  Quad :: !(Mat x1 y1 a) -> !(Mat x2 y1 a) ->
          !(Mat x1 y2 a) -> !(Mat x2 y2 a) ->
          Mat ('Bin x1 x2) ('Bin y1 y2) a
  Zero :: Mat x y a
  One :: !a -> Mat 'Leaf 'Leaf a
  Row :: Mat x1 'Leaf a -> Mat x2 'Leaf a -> Mat ('Bin x1 x2) 'Leaf a
  Col :: Mat 'Leaf y1 a -> Mat 'Leaf y2 a -> Mat 'Leaf ('Bin y1 y2) a

data Vec :: Shape -> *  -> * where
  ZeroV :: Vec x a
  BinV :: Vec x a -> Vec y a -> Vec ('Bin x y) a
  OneV :: a -> Vec 'Leaf a

infixl 7 ∙

-- | Product of sparse matrices
(∙) :: RingZ a => Mat x y a -> Mat z x a -> Mat z y a
Zero ∙ _ = Zero
_ ∙ Zero = Zero
One x ∙ One x' = Closure.one (x * x')
One x ∙ Row a b = row (One x ∙ a) (One x ∙ b)
Col a b ∙ One x = col (a ∙ One x) (b ∙ One x)
Row a b ∙ Col a' b' = a ∙ a' + b ∙ b'
Col a b ∙ Row a' b' = quad (a ∙ a') (a ∙ b') (b ∙ a') (b ∙ b')
Row a b ∙ Quad a' b' c' d' = row (a ∙ a' + b ∙ c') (a ∙ b' + b ∙ d')
Quad a b c d ∙ Col a' c' = col (a ∙ a' + b ∙ c') (c ∙ a' + d ∙ c')
Quad a b c d ∙ Quad a' b' c' d' =
  quad (a ∙ a' + b ∙ c') (a ∙ b' + b ∙ d')
       (c ∙ a' + d ∙ c') (c ∙ b' + d ∙ d')

instance (Additive a, ZeroTest a) => Additive (Mat x y a) where
  zero = Zero
  Zero + x = x
  x + Zero = x
  Quad a b c d + Quad a' b' c' d' = quad (a + a') (b + b') (c + c') (d + d')
  One x + One x' = Closure.one (x + x')
  Row x y + Row x' y' = row (x + x') (y + y')
  Col x y + Col x' y' = col (x + x') (y + y')


instance (ZeroTest a, AbelianAdditive a) => AbelianAdditive (Mat x y a) where

row :: Mat x1 'Leaf a -> Mat x2 'Leaf a -> Mat ('Bin x1 x2) 'Leaf a
row Zero Zero = Zero
row x y = Row x y

col :: Mat 'Leaf y1 a -> Mat 'Leaf y2 a -> Mat 'Leaf ('Bin y1 y2) a
col Zero Zero = Zero
col x y = Col x y

quad :: Mat x1 y1 a
          -> Mat x2 y1 a
          -> Mat x1 y2 a
          -> Mat x2 y2 a
          -> Mat ('Bin x1 x2) ('Bin y1 y2) a
quad Zero Zero Zero Zero = Zero
quad a b c d = Quad a b c d

one :: ZeroTest a => a -> Mat 'Leaf 'Leaf a
one x | isZero x = Zero
      | otherwise = One x

closure :: RingZ a => Mat x x a -> Mat x x a
closure Zero = Zero
closure (One a) = One a
closure (Quad a b c d) = Quad (ac + b ∙ deltac ∙ c') (b' ∙ deltac)
                              (deltac ∙ c') deltac
  where
    b' = ac ∙ b
    c' = c ∙ ac
    delta = d + c ∙ ac ∙ b
    deltac = closure delta
    ac = closure a

sz' :: Shape' s -> Int
sz' Leaf' = 1
sz' (Bin' x _ _) = x

bin' :: Shape' s -> Shape' s' -> Shape' ('Bin s s')
bin' s s' = Bin' (sz' s + sz' s') s s'

foldIx :: Int -> Int -> (Int -> Int -> a -> b) -> b -> (b -> b -> b) -> (b -> b -> b) ->
          Max x y a -> b
foldIx u v h Zero

-- | Lookup in a vector
lk :: AbelianGroup a => Int -> Shape' x -> Vec x a -> a
lk n _ Z = zero
lk 0 Leaf' (O x) = x
lk i (Bin' _ s s') (x :! x')
  | i < sz' s  = lk i s x
  | otherwise = lk (i - sz' s) s' x'

mkShape :: Int -> SomeShape
mkShape 1 = S (bin' Leaf' Leaf')
mkShape 2 = S (bin' (bin' Leaf' Leaf') Leaf')
mkShape n = case (mkShape n'1, mkShape n'2) of
  (S x, S y) -> S (bin' x y)
  where n'1 = n `div` 2
        n'2 = n - n'1 - 1
