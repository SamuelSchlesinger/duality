{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
module Control.Duality where

import Control.Monad
import Data.Functor.Identity
import Data.Functor.Compose

-- Inspired by this post by Ed Kmett
--------------------------------------------------------------------------------
-- http://comonad.com/reader/2008/the-cofree-comonad-and-the-expression-problem/
--------------------------------------------------------------------------------
-- I strongly recommend you go read it, as it is an exposition of the ideas
-- that I am trying to understand in code.

type family Co (f :: k1) :: k2

class (Functor f, Functor g) => Dual f g where
  zap :: (a -> b -> c) -> f a -> g b -> c
  default zap :: Dual g f => (a -> b -> c) -> f a -> g b -> c
  zap z = flip (zap (flip z))

instance Dual Identity Identity where
  zap z (Identity a) (Identity b) = z a b

type instance Co Identity = Identity

type instance Co ((->) a) = ((,) a)
instance Dual ((->) a) ((,) a) where
  zap z f (a, b) = z (f a) b

type instance Co ((,) a) = ((->) a)
instance Dual ((,) x) ((->) x)

type instance Co (Free f) = CoFree (Co f)
instance Dual f g => Dual (Free f) (CoFree g) where
  zap z (Pure a) (CoFree b bs) = z a b
  zap z (Free a) (CoFree b bs) = zap (zap z) a bs

type instance Co (CoFree f) = Free
instance Dual g f => Dual (CoFree f) (Free g)

data (f + g) x = L (f x) | R (g x)

instance (Functor f, Functor g) => Functor (f + g) where
  fmap f (L x) = L (fmap f x)
  fmap f (R x) = R (fmap f x)

data (f & g) x = P (f x) (g x)

instance (Functor f, Functor g) => Functor (f & g) where
  fmap f (P a b) = P (fmap f a) (fmap f b)

type instance Co (f + f') = Co f & Co f'
instance (Dual f g, Dual f' g') => Dual (f + f') (g & g') where
  zap z (L x) (P a b) = zap z x a
  zap z (R x) (P a b) = zap z x b

type instance Co (f & f') = Co f + Co f'
instance (Dual f g, Dual f' g') => Dual (g & g') (f + f')

type instance Co (Compose f f') = Compose (Co f) (Co f')
instance (Dual f g, Dual f' g', Functor f, Functor f', Functor g, Functor g') => Dual (Compose f f') (Compose g g') where
  zap z (Compose f) (Compose g) = zap (zap z) f g

type State   a = Compose ((->) a) ((,) a)
type CoState a = Compose ((,) a)  ((->) a)

type Reader   a = ((->) a)
type CoReader a = ((,) a)

type Writer   a = ((,) a)
type CoWriter a = ((->) a) 

-- QUESTION: Can you do anything with the fixpoints of dual functors?
-- I feel like you should be able to? Help! Aha! Fixpoints of functor
-- functors!

-- Now we work in the category with functors as the objects and natural transformations
-- between functors as the arrows.
class Bifunctor t where
  bimap :: forall f f' g g' a. 
    ( Functor f
    , Functor f'
    , Functor g
    , Functor g' ) => (forall x. f x -> f' x)
                   -> (forall x. g x -> g' x)
                   -> t f g a -> t f' g' a 

instance Bifunctor (&) where
  bimap n n' (P f g) = P (n f) (n' g)

instance Bifunctor (+) where
  bimap n _  (L f) = L (n  f)
  bimap _ n' (R f) = R (n' f)

instance Bifunctor Compose where
  bimap n n' (Compose c) = Compose (n (fmap n' c))

class (Bifunctor t, Bifunctor s) => Bidual t s where
  bizap :: forall f f' g g' h a. 
       (Functor f, Functor g, Functor h)
    => (forall x. f x -> g x -> h x) 
    -> (forall x. f' x -> g' x -> h x) 
    -> t f f' a
    -> s g g' a
    -> h a
  default bizap :: forall f f' g g' h a. 
       (Functor f, Functor g, Functor h, Bidual s t)
    => (forall x. f x -> g x -> h x) 
    -> (forall x. f' x -> g' x -> h x) 
    -> t f f' a
    -> s g g' a
    -> h a
  bizap n m = flip (bizap (flip n) (flip m))

type instance Co (+) = (&)
instance Bidual (+) (&) where
  bizap n _  (L a) (P b _) = (n  a) b
  bizap _ n' (R a) (P _ b) = (n' a) b

type instance Co (&) = (+) 
instance Bidual (&) (+)

newtype ComposeT h t (f :: * -> *) (g :: * -> *) a = ComposeT (h (t f g a))

instance (Functor h, Bifunctor t) => Bifunctor (ComposeT h t) where
  bimap n n' (ComposeT h) = ComposeT (fmap (bimap n n') h)

type instance Co (ComposeT h t) = ComposeT (Co h) (Co t)
instance (Dual h h', Bidual t t') => Bidual (ComposeT h t) (ComposeT h' t') where
  bizap n n' (ComposeT a) (ComposeT b) = zap (bizap n n') a b

-- newtype ComposeS h t (f :: * -> *) (g :: * -> *) a = ComposeS (t f g (h a))

-- instance (Functor h, Bifunctor t) => Bifunctor (ComposeS h t) where
--   bimap n n' (ComposeS h) = ComposeS (bimap n n' h)

-- instance (Dual h h', Bidual t t') => Bidual (ComposeS h t) (ComposeS h' t') where
-- Now this is weird...

newtype FixT t a = FixT (t (FixT t) a)

instance (forall f. Functor f => Functor (t f)) => Functor (FixT t) where
  fmap f (FixT x) = FixT (fmap f x)

type Machine m a b = FixT (ComposeT ((->) a) (&) m) b

example :: Machine IO Int ()
example = FixT . ComposeT $ \n -> P (print n) example

type instance Co (FixT f) = Co (FixT (Co f)) 
instance (forall f f'. Dual f f' => Dual (t f) (t' f') 
        , forall f. Functor f => Functor (t' f)
        , forall f. Functor f => Functor (t f) ) => Dual (FixT t) (FixT t') where
  zap z (FixT a) (FixT b) = zap z a b

newtype Codensity m a = Codensity (forall b. (a -> m b) -> m b)

instance Functor (Codensity m) where
  fmap f (Codensity g) = Codensity \c -> g (c . f)

data Density m a where 
  Density :: (m b -> a) -> (m b) -> Density m a

instance Functor (Density m) where
  fmap f (Density g b) = Density (f . g) b

type instance Co Density = Codensity
instance (Comonad w, Monad m, Dual w m) => Dual (Density w) (Codensity m) where
  zap z (Density x g) (Codensity y) = zap z (extend x g) (y return)

type instance Co Codensity = Density
instance (Comonad w, Monad m, Dual w m) => Dual (Codensity m) (Density w) 

-- Summary:
--
-- So now, I can write a free monad, a dual cofree comonadic context in which 
-- it will run, take the codensity/density transforms of each, and let the
-- computer do its thing.
--
-- Let's do it!

type Conversation a = ((,) a) + ((->) a)

speak :: b -> Free (Conversation b) a -> Free (Conversation b) a
speak str = Free . L . ((,) str)

listen :: (b -> Free (Conversation b) a) -> Free (Conversation b) a
listen = Free . R

discussion :: Free (Conversation (Int, Int)) String
discussion = listen 
  \(x, y) -> if min x y < 10 
          then speak (4,333333333) discussion
          else return "success!"

coordinates :: (Int, Int) -> Co (Free (Conversation (Int, Int))) (Int, Int)
coordinates (n, m) = CoFree (n, m) (P (\str -> coordinates (n + 1, m)) ((n, m), coordinates (n, m + 1)))

-- Here, we output the "coordinates" I got to in my discussion... Notice
-- that I can feed different contexts into my contextual computation, these
-- contexts themselves giving back some summary of what went on,
-- positionally.

test :: (Int, Int)
test = zap (flip const) discussion (coordinates (0, 0))

-- you can record the input to all of your free monadic combinators, roll
-- it up into a cofree monad, and replay history in a pure way to figure
-- stuff out...

-- Things lieth beneath which are grokkable elsewhere
--------------------------------------------------------------------------------

newtype Fix f = Fix (f (Fix f))

data Free f a = Free (f (Free f a)) | Pure a

instance Functor f => Functor (Free f) where
  fmap f (Free a) = Free (fmap (fmap f) a)
  fmap f (Pure a) = Pure (f a)

instance Functor f => Applicative (Free f) where
  Free f <*> a = Free (fmap (<*> a) f)
  Pure f <*> a = fmap f a
  pure = Pure

instance Functor f => Monad (Free f) where
  Free a >>= f = Free (fmap (>>= f) a)
  Pure a >>= f = f a

data CoFree f a = CoFree a (f (CoFree f a))

instance Functor f => Functor (CoFree f) where
  fmap f (CoFree a as) = CoFree (f a) (fmap (fmap f) as)

class Functor w => Comonad w where
  extend :: (w a -> b) -> w a -> w b
  duplicate :: w a -> w (w a)
  extract :: w a -> a

instance Functor f => Comonad (CoFree f) where
  extend f c@(CoFree _ as) = CoFree (f c) (fmap (extend f) as) 
  duplicate c@(CoFree _ as) = CoFree c (fmap duplicate as)
  extract (CoFree a _) = a
