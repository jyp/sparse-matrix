{-# LANGUAGE DataKinds, KindSignatures, GADTs, ConstraintKinds, FlexibleInstances #-}

module Closure where

import Algebra.Classes
import Prelude (Bool(..),otherwise,Int,print,Ord(..),Functor(..))

type RingZ a = (Ring a, ZeroTest a)

class Ring a => Closed a where
  -- closure a = one + a + a*a + a*a*a + ...
  closure :: a -> a

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
  Single :: !a -> Mat 'Leaf 'Leaf a

  Row :: Mat x1 'Leaf a -> Mat x2 'Leaf a -> Mat ('Bin x1 x2) 'Leaf a
  Col :: Mat 'Leaf y1 a -> Mat 'Leaf y2 a -> Mat 'Leaf ('Bin y1 y2) a

type Row x a = Mat x 'Leaf a
type Col x a = Mat 'Leaf x a

transpose :: Mat x y a -> Mat y x a
transpose Zero = Zero
-- transpose One = One
transpose (Single a) = Single a
transpose (Row a b) = Col (transpose a) (transpose b)
transpose (Col a b) = Row (transpose a) (transpose b)
transpose (Quad a b c d) = Quad (transpose a) (transpose  c)
                                (transpose b) (transpose d)

infixl 7 ∙

-- | Attn! this instance supposes that the map preserves zeros.
instance Functor (Mat x y) where
  fmap f Zero = Zero
  fmap f (Single a) = Single (f a)
  fmap f (Row a b) = Row (fmap f a) (fmap f b)
  fmap f (Col a b) = Col (fmap f a) (fmap f b)
  fmap f (Quad a b c d) = Quad (fmap f a) (fmap f b) (fmap f c) (fmap f d)

-- | Product of sparse matrices
(∙) :: RingZ a => Mat x y a -> Mat z x a -> Mat z y a
Zero ∙ _ = Zero
_ ∙ Zero = Zero
Single x ∙ Single x' = oneM (x * x')
Single x ∙ Row a b = row (Single x ∙ a) (Single x ∙ b)
Col a b ∙ Single x = col (a ∙ Single x) (b ∙ Single x)
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
  Single x + Single x' = oneM (x + x')
  Row x y + Row x' y' = row (x + x') (y + y')
  Col x y + Col x' y' = col (x + x') (y + y')

instance (ZeroTest a, Group a) => Group (Mat x y a) where
  negate = fmap negate


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

oneM :: ZeroTest a => a -> Mat 'Leaf 'Leaf a
oneM x | isZero x = Zero
      | otherwise = Single x

instance RingZ a => Multiplicative (Mat x x a) where
  (*) = (∙)
  -- one = _

instance RingZ a => Ring (Mat x x a) where


instance (Closed a,ZeroTest a) => Closed (Mat x x a) where
  -- closure :: RingZ a => Mat x x a -> Mat x x a
  closure Zero = Zero
  -- closure One = One
  closure (Single a) = Single (closure a)
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
          Shape' x -> Shape' y -> Mat x y a -> b
foldIx x y u z (<|>) (<->) _ _ Zero = z
foldIx x y u z (<|>) (<->) w h (Single a) = u x y a
foldIx x y u z (<|>) (<->) (Bin' _ wa wb) Leaf' (Row a b) =
       foldIx x y u z (<|>) (<->) wa Leaf' a
   <|> foldIx (x + sz' wa) y u z (<|>) (<->) wb Leaf' b
foldIx x y u z (<|>) (<->) Leaf' (Bin' _ ha hb) (Col a b) =
       foldIx x y u z (<|>) (<->) Leaf' ha a
   <-> foldIx x (y + sz' ha) u z (<|>) (<->) Leaf' hb b
foldIx x y u z (<|>) (<->) (Bin' _ wa wb) (Bin' _ ha hb) (Quad a b c d) =
       (foldIx x y u z (<|>) (<->) wa ha a <|>
        foldIx (x + sz' wa) y u z (<|>) (<->) wb ha b)
   <-> (foldIx x (y + sz' ha) u z (<|>) (<->) wa hb c <|>
        foldIx (x + sz' wa) (y + sz' ha) u z (<|>) (<->) wb hb d)

lookupRow :: Int -> Shape' y -> Mat x y a -> Row x a
lookupRow _ _ Zero = Zero
lookupRow y Leaf' m = m
lookupRow i (Bin' _ wa wb) (Quad a b c d)
  | i  < sz' wa = Row (lookupRow i wa a) (lookupRow i wa b)
  | otherwise = Row (lookupRow (i-sz' wa) wb c) (lookupRow (i-sz' wa) wb d)

lookupCol :: Int -> Shape' x -> Mat x y a -> Col y a
lookupCol i w m = transpose (lookupRow i w (transpose m))


mkShape :: Int -> SomeShape
mkShape 1 = S (bin' Leaf' Leaf')
mkShape 2 = S (bin' (bin' Leaf' Leaf') Leaf')
mkShape n = case (mkShape n'1, mkShape n'2) of
  (S x, S y) -> S (bin' x y)
  where n'1 = n `div` 2
        n'2 = n - n'1 - 1
