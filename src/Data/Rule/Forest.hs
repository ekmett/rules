{-# LANGUAGE LambdaCase, DeriveDataTypeable #-}
module Data.Rule.Forest where

import Control.Applicative
import Control.Monad (when)
import Control.Monad.ST
import Data.Function (on)
import Data.STRef
import Data.Typeable

data Link s a
  = Self  { linkRank :: {-# UNPACK #-} !Int, _linkValue :: a }
  | Other { linkRank :: {-# UNPACK #-} !Int, _linkNode :: {-# UNPACK #-} !(Node s a) }
  deriving Typeable

newtype Node s a = Node { nodeLink :: STRef s (Link s a) }
  deriving Typeable

instance Eq (Node s a) where
  (==) = (==) `on` nodeLink

node :: a -> ST s (Node s a)
node a = Node <$> newSTRef (Self 0 a)

find :: Node s a -> ST s (Node s a)
find n@(Node r) = readSTRef r >>= \case
  Self _ _ -> return n
  Other i n' -> do
    n'' <- find n'
    n'' <$ writeSTRef r (Other i n'')

find' :: Node s a -> ST s (Node s a, Int, a)
find' n@(Node r) = readSTRef r >>= \case
  Self i a -> return (n, i, a)
  Other i n' -> do
    (n'',_,a) <- find' n'
    (n'',i,a) <$ writeSTRef r (Other i n'')

-- merge with a commutative semigroup
union :: (a -> a -> a) -> Node s a -> Node s a -> ST s ()
union f l r = do
  (lz, lr, a) <- find' l
  (rz, rr, b) <- find' r
  when (lz /= rz) $ do
    let fab = f a b
    if lr < rr then do
      writeSTRef (nodeLink l) $ Other lr rz
      writeSTRef (nodeLink r) $ Self rr fab
    else do
      writeSTRef (nodeLink l) $! Self (if lr == rr then lr + 1 else lr) fab
      writeSTRef (nodeLink r) $ Other rr lz

same :: Node s a -> Node s a -> ST s Bool
same = liftA2 (==) `on` find
