{-# LANGUAGE DefaultSignatures, FlexibleContexts, TypeOperators #-}
module Data.Rule.Alignable
  ( Alignable(..)
  , GAlignable
  ) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Comonad.Cofree
import Control.Comonad.Env
import Control.Monad.Free
import Control.Monad.Trans.Either
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Writer
import Control.Parallel (pseq)
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Coproduct
import Data.Functor.Reverse
import Data.Tuple (swap)
import GHC.Generics

--------------------------------------------------------------------------------
-- * Alignable
--------------------------------------------------------------------------------

-- | Shapes we can try to match exactly and glue with applicative side-effects.

class Alignable t where
  align :: Alternative m => (a -> b -> m c) -> t a -> t b -> m (t c)
  default align :: (Generic1 t, GAlignable (Rep1 t), Alternative m) => (a -> b -> m c) -> t a -> t b -> m (t c)
  align f xs ys = to1 <$> galign f (from1 xs) (from1 ys)

instance Alignable Maybe where
  align f (Just a) (Just b) = Just <$> f a b
  align _ _ _ = empty

instance Alignable [] where
  align f (x:xs) (y:ys) = (:) <$> f x y <*>  align f xs ys
  align _ _ _           = empty

instance Eq e => Alignable (Either e) where
  align f (Right a) (Right b)        = Right <$> f a b
  align _ (Left a) (Left b) | a == b = pure (Left a)
  align _ _ _                        = empty

instance Eq e => Alignable ((,) e) where
  align f (e, a) (e', b) 
    | e == e' = (,) e <$> f a b
    | otherwise = empty

instance (Alignable f, Alignable g) => Alignable (Compose f g) where
  align f (Compose xs) (Compose ys) = Compose <$> align (align f) xs ys

instance Alignable f => Alignable (IdentityT f) where
  align f (IdentityT xs) (IdentityT ys) = IdentityT <$> align f xs ys

instance Alignable Identity where
  align f (Identity a) (Identity b) = Identity <$> f a b
  
instance (Alignable m, Eq e) => Alignable (WriterT e m) where
  align f (WriterT xs) (WriterT ys) = WriterT <$> align (\as bs -> swap <$> align f (swap as) (swap bs)) xs ys

instance (Alignable m, Eq e) => Alignable (EitherT e m) where
  align f (EitherT xs) (EitherT ys) = EitherT <$> align (align f) xs ys

instance (Alignable f, Alignable g) => Alignable (Product f g) where
  align f (Pair as as') (Pair bs bs') = Pair <$> align f as bs <*> align f as' bs'

instance (Alignable f, Alignable g) => Alignable (Coproduct f g) where
  align f (Coproduct (Left xs)) (Coproduct (Left ys)) = Coproduct . Left <$> align f xs ys
  align f (Coproduct (Right xs)) (Coproduct (Right ys)) = Coproduct . Right <$> align f xs ys
  align _ _ _ = empty

instance Alignable f => Alignable (Free f) where
  align f (Pure a) (Pure b) = Pure <$> f a b
  align f (Free as) (Free bs) = Free <$> align (align f) as bs
  align _ _ _ = empty

instance Alignable f => Alignable (Cofree f) where
  align f (a :< as) (b :< bs) = (:<) <$> f a b <*> align (align f) as bs

instance (Alignable w, Eq e) => Alignable (EnvT e w) where
  align f (EnvT e wa) (EnvT e' wb)
    | e == e' = EnvT e <$> align f wa wb
    | otherwise = empty

instance Alignable f => Alignable (Reverse f) where
  align f (Reverse as) (Reverse bs) = fmap Reverse . forwards $ align (\a b -> Backwards $ f a b) as bs
  
--------------------------------------------------------------------------------
-- * Generic Alignable
--------------------------------------------------------------------------------

class GAlignable t where
  galign :: Alternative m => (a -> b -> m c) -> t a -> t b -> m (t c)

instance GAlignable U1 where
  galign _ U1 U1 = pure U1

instance GAlignable V1 where
  galign _ as _ = as `pseq` undefined

instance (GAlignable f, GAlignable g) => GAlignable (f :*: g) where
  galign f (as :*: as') (bs :*: bs') = (:*:) <$> galign f as bs <*> galign f as' bs'

instance (GAlignable f, GAlignable g) => GAlignable (f :+: g) where
  galign f (L1 as) (L1 bs) = L1 <$> galign f as bs
  galign f (R1 as) (R1 bs) = R1 <$> galign f as bs
  galign _ _ _             = empty

instance GAlignable f => GAlignable (M1 i c f) where
  galign f (M1 as) (M1 bs) = M1 <$> galign f as bs

instance Eq c => GAlignable (K1 i c) where
  galign _ (K1 x) (K1 y)
    | x == y    = pure (K1 x)
    | otherwise = empty

instance Alignable f => GAlignable (Rec1 f) where
  galign f (Rec1 as) (Rec1 bs) = Rec1 <$> align f as bs

instance GAlignable Par1 where
  galign f (Par1 a) (Par1 b) = Par1 <$> f a b

