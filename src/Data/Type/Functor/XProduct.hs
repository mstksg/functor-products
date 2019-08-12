{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Functor.XProduct (
    XProd
  , fromXProd
  , toXProd
  -- * Functions
  , mapProdX, mapProdXEndo
  , imapProdX, zipWithProdX
  , ixProdX, traverseProdX, traverseProdXEndo, itraverseProdX
  , foldMapProdX, ifoldMapProdX
  -- * Instances
  , XRec, pattern (::&), pattern XRNil
  , XMaybe, pattern XNothing, pattern XJust
  , XEither, pattern XLeft, pattern XRight
  , XNERec, pattern (::&|)
  , XTup, pattern XSnd
  , XIdentity, pattern XIdentity
  ) where

import           Data.Functor.Identity
import           Data.Kind
import           Data.List.NonEmpty        (NonEmpty(..))
import           Data.Type.Functor.Product
import           Data.Vinyl
import           Data.Vinyl.XRec
import           Lens.Micro
import qualified Data.Vinyl.Functor        as V

type XProd f g = (Prod f (XData g) :: f k -> Type)

fromXProd :: forall f g as. (FProd f, PureProdC f (IsoHKD g) as) => XProd f g as -> Prod f g as
fromXProd = zipWithProd (\(V.Lift u) x -> u x)
              (pureProdC @_ @(IsoHKD g) (V.Lift (unHKD . unX)))

toXProd :: forall f g as. (FProd f, PureProdC f (IsoHKD g) as) => Prod f g as -> XProd f g as
toXProd = zipWithProd (\(V.Lift u) x -> u x)
              (pureProdC @_ @(IsoHKD g) (V.Lift (XData . toHKD)))

mapProdX
    :: forall f g h as. FProd f
    => (forall a. HKD g a -> HKD h a)
    -> XProd f g as
    -> XProd f h as
mapProdX f = mapProd $ \(XData x :: XData g a) -> XData (f @a x)

mapProdXEndo
    :: forall f g as. FProd f
    => (forall a. HKD g a -> HKD g a)
    -> XProd f g as
    -> XProd f g as
mapProdXEndo f = mapProd $ \(XData x :: XData g a) -> XData (f @a x)

imapProdX
    :: forall f g h as. FProd f
    => (forall a. Elem f as a -> HKD g a -> HKD h a)
    -> XProd f g as
    -> XProd f h as
imapProdX f = imapProd $ \i -> XData . f i . unX

zipWithProdX
    :: forall f g h j as. FProd f
    => (forall a. HKD g a -> HKD h a -> HKD j a)
    -> XProd f g as
    -> XProd f h as
    -> XProd f j as
zipWithProdX f = zipWithProd $ \(XData x :: XData g a) (XData y) -> XData (f @a x y)

ixProdX
    :: FProd f
    => Elem f as a
    -> Lens' (XProd f g as) (HKD g a)
ixProdX i = ixProd i . (\f (XData x) -> XData <$> f x)

traverseProdX
    :: forall f g h m as. (FProd f, Applicative m)
    => (forall a. HKD g a -> m (HKD h a))
    -> XProd f g as
    -> m (XProd f h as)
traverseProdX f = traverseProd $ \(XData x :: XData g a) -> XData <$> f @a x

traverseProdXEndo
    :: forall f g m as. (FProd f, Applicative m)
    => (forall a. HKD g a -> m (HKD g a))
    -> XProd f g as
    -> m (XProd f g as)
traverseProdXEndo f = traverseProd $ \(XData x :: XData g a) -> XData <$> f @a x

itraverseProdX
    :: forall f g h m as. (FProd f, Applicative m)
    => (forall a. Elem f as a -> HKD g a -> m (HKD h a))
    -> XProd f g as
    -> m (XProd f h as)
itraverseProdX f = itraverseProd $ \i -> fmap XData . f i . unX

foldMapProdX
    :: forall f g m as. (FProd f, Monoid m)
    => (forall a. HKD g a -> m)
    -> XProd f g as
    -> m
foldMapProdX f = foldMapProd $ \(XData x :: XData g a) -> f @a x

ifoldMapProdX
    :: forall f g m as. (FProd f, Monoid m)
    => (forall a. Elem f as a -> HKD g a -> m)
    -> XProd f g as
    -> m
ifoldMapProdX f = ifoldMapProd $ \i -> f i . unX

type XMaybe f    = PMaybe (XData f)
type XEither f   = PEither (XData f)
type XNERec f    = NERec (XData f)
type XTup f      = PTup (XData f)
type XIdentity f = PIdentity (XData f)

pattern XNothing :: XMaybe f 'Nothing
pattern XNothing = PNothing

pattern XJust :: HKD f a -> XMaybe f ('Just a)
pattern XJust x = PJust (XData x)

pattern XLeft :: XEither f ('Left e)
pattern XLeft = PLeft

pattern XRight :: HKD f a -> XEither f ('Right a)
pattern XRight x = PRight (XData x)

pattern (::&|) :: HKD f a -> XRec f as -> XNERec f (a ':| as)
pattern x ::&| xs = XData x :&| xs

pattern XSnd :: HKD f a -> XTup f '(w, a)
pattern XSnd x = PSnd (XData x)

pattern XIdentity :: HKD f a -> XIdentity f ('Identity a)
pattern XIdentity x = PIdentity (XData x)
