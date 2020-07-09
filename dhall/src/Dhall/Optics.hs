{-| This module contains some useful utilities copy-and-pasted from the @lens@
    library to avoid a dependency which are used internally and also re-exported
    for convenience
-}

module Dhall.Optics
    ( -- * Utilities
      rewriteOf
    , transformOf
    , rewriteMOf
    , transformMOf
    , mapMOf
    , universeOf
    , cosmosOf
    ) where

import Control.Applicative (WrappedMonad(..))
import Data.Profunctor.Unsafe ((#.))
import Lens.Family (ASetter, FoldLike', LensLike, LensLike', over, views)

-- | Identical to @"Control.Lens".`Control.Lens.rewriteOf`@
rewriteOf :: ASetter a b a b -> (b -> Maybe a) -> a -> b
rewriteOf l f = go
  where
    go = transformOf l (\x -> maybe x go (f x))
{-# INLINE rewriteOf #-}

-- | Identical to @"Control.Lens".`Control.Lens.transformOf`@
transformOf :: ASetter a b a b -> (b -> b) -> a -> b
transformOf l f = go
  where
    go = f . over l go
{-# INLINE transformOf #-}

-- | Identical to @"Control.Lens".`Control.Lens.rewriteMOf`@
rewriteMOf
    :: Monad m
    => LensLike (WrappedMonad m) a b a b -> (b -> m (Maybe a)) -> a -> m b
rewriteMOf l f = go
  where
    go = transformMOf l (\x -> f x >>= maybe (return x) go)
{-# INLINE rewriteMOf #-}

-- | Identical to @"Control.Lens".`Control.Lens.transformMOf`@
transformMOf
    :: Monad m => LensLike (WrappedMonad m) a b a b -> (b -> m b) -> a -> m b
transformMOf l f = go
  where
    go t = mapMOf l go t >>= f
{-# INLINE transformMOf #-}

-- | Identical to @"Control.Lens".`Control.Lens.mapMOf`@
mapMOf :: LensLike (WrappedMonad m) s t a b -> (a -> m b) -> s -> m t
mapMOf l cmd = unwrapMonad #. l (WrapMonad #. cmd)
{-# INLINE mapMOf #-}

-- | Identical to @"Control.Lens".`Control.Lens.universeOf`@
universeOf :: FoldLike' [a] a a -> a -> [a]
universeOf l = go
  where
    go a = a : views l go a

-- | Identical to @"Control.Lens".`Control.Lens.cosmosOf`@
cosmosOf :: Applicative f => LensLike' f a a -> LensLike' f a a
cosmosOf d f s = f s *> d (cosmosOf d f) s
