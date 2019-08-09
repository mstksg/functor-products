{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Type.Functor.Product (
  -- * Classes
    FProd(..), Shape
  , PureProd(..), pureShape
  , PureProdC(..), ReifyConstraintProd(..)
  , AllConstrainedProd
  -- ** Functions
  , indexProd, indexSing
  , mapProd, foldMapProd, hmap, zipProd
  , imapProd, itraverseProd, ifoldMapProd
  , ifoldMapSing, foldMapSing
  -- * Instances
  , Rec(..), Index(..)
  , PMaybe(..), IJust(..)
  , PEither(..), IRight(..)
  , NERec(..), NEIndex(..)
  , PTup(..), ISnd(..)
  , PIdentity(..), IIdentity(..)
  , sameIndexVal, sameNEIndexVal
  -- * Singletons
  , SIndex(..), SIJust(..), SIRight(..), SNEIndex(..), SISnd(..), SIIdentity(..)
  , Sing (SIndex', SIJust', SIRight', SNEIndex', SISnd', SIIdentity')
  -- * Defunctionalization symbols
  , ElemSym0, ElemSym1, ElemSym2
  , ProdSym0, ProdSym1, ProdSym2
  ) where

import           Control.Applicative
import           Data.Functor.Classes
import           Data.Functor.Identity
import           Data.Kind
import           Data.List.NonEmpty                      (NonEmpty(..))
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Singletons.Prelude hiding          (Elem, ElemSym0, ElemSym1, ElemSym2)
import           Data.Singletons.Prelude.Foldable hiding (Elem, ElemSym0, ElemSym1, ElemSym2)
import           Data.Singletons.Prelude.Identity
import           Data.Vinyl hiding                       ((:~:))
import           GHC.Generics                            ((:*:)(..))
import           Lens.Micro hiding                       ((%~))
import           Lens.Micro.Extras
import           Unsafe.Coerce
import qualified Data.Singletons.Prelude.List.NonEmpty   as NE
import qualified Data.Vinyl.Functor                      as V
import qualified Data.Vinyl.TypeLevel                    as V

fmapIdent :: Fmap IdSym0 as :~: as
fmapIdent = unsafeCoerce Refl

type Shape f = (Prod f Proxy :: f k -> Type)

class (PFunctor f, SFunctor f, PFoldable f, SFoldable f) => FProd (f :: Type -> Type) where
    type Elem  f = (i :: f k -> k -> Type) | i -> f
    type Prod  f = (p :: (k -> Type) -> f k -> Type) | p -> f

    singProd :: Sing as -> Prod f Sing as

    withIndices
        :: Prod f g as
        -> Prod f (Elem f as :*: g) as

    traverseProd
        :: forall g h as m. Applicative m
        => (forall a. g a -> m (h a))
        -> Prod f g as
        -> m (Prod f h as)
    traverseProd = case fmapIdent @as of
      Refl -> htraverse (sing @IdSym0)

    zipWithProd
        :: (forall a. g a -> h a -> j a)
        -> Prod f g as
        -> Prod f h as
        -> Prod f j as
    zipWithProd f xs ys = imapProd (\i x -> f x (indexProd i ys)) xs

    htraverse
        :: Applicative m
        => Sing ff
        -> (forall a. g a -> m (h (ff @@ a)))
        -> Prod f g as
        -> m (Prod f h (Fmap ff as))

    ixProd
        :: Elem f as a
        -> Lens' (Prod f g as) (g a)

    toRec :: Prod f g as -> Rec g (ToList as)

class PureProd (f :: Type -> Type) (as :: f k) where
    pureProd :: (forall a. g a) -> Prod f g as

class PureProdC (f :: Type -> Type) c (as :: f k) where
    pureProdC :: (forall a. c a => g a) -> Prod f g as

class ReifyConstraintProd (f :: Type -> Type) c (g :: k -> Type) (as :: f k) where
    reifyConstraintProd :: Prod f g as -> Prod f (Dict c V.:. g) as

data ElemSym0 (f :: Type -> Type) :: f k ~> k ~> Type
data ElemSym1 (f :: Type -> Type) :: f k -> k ~> Type
type ElemSym2 (f :: Type -> Type) (as :: f k) (a :: k) = Elem f as a

type instance Apply (ElemSym0 f) as = ElemSym1 f as
type instance Apply (ElemSym1 f as) a = Elem f as a

data ProdSym0 (f :: Type -> Type) :: (k -> Type) ~> f k ~> Type
data ProdSym1 (f :: Type -> Type) :: (k -> Type) -> f k ~> Type
type ProdSym2 (f :: Type -> Type) (g :: k -> Type) (as :: f k) = Prod f g as

type instance Apply (ProdSym0 f) g = ProdSym1 f g
type instance Apply (ProdSym1 f g) as = Prod f g as

type AllConstrainedProd c as = V.AllConstrained c (ToList as)

pureShape :: PureProd f as => Shape f as
pureShape = pureProd Proxy

mapProd
    :: FProd f
    => (forall a. g a -> h a)
    -> Prod f g as
    -> Prod f h as
mapProd f = runIdentity . traverseProd (Identity . f)

zipProd
    :: FProd f
    => Prod f g as
    -> Prod f h as
    -> Prod f (g :*: h) as
zipProd = zipWithProd (:*:)

hmap
    :: FProd f
    => Sing ff
    -> (forall a. g a -> h (ff @@ a))
    -> Prod f g as
    -> Prod f h (Fmap ff as)
hmap ff f = runIdentity . htraverse ff (Identity . f)

imapProd
    :: FProd f
    => (forall a. Elem f as a -> g a -> h a)
    -> Prod f g as
    -> Prod f h as
imapProd f = mapProd (\(i :*: x) -> f i x) . withIndices

-- | Extract the item from the container witnessed by the 'Elem'
indexSing
    :: forall f as a. FProd f
    => Elem f as a        -- ^ Witness
    -> Sing as            -- ^ Collection
    -> Sing a
indexSing i = indexProd i . singProd

indexProd
    :: FProd f
    => Elem f as a
    -> Prod f g as
    -> g a
indexProd i = view (ixProd i)

itraverseProd
    :: (FProd f, Applicative m)
    => (forall a. Elem f as a -> g a -> m (h a))
    -> Prod f g as
    -> m (Prod f h as)
itraverseProd f = traverseProd (\(i :*: x) -> f i x) . withIndices

ifoldMapProd
    :: (FProd f, Monoid m)
    => (forall a. Elem f as a -> g a -> m)
    -> Prod f g as
    -> m
ifoldMapProd f = getConst . itraverseProd (\i -> Const . f i)

foldMapProd
    :: (FProd f, Monoid m)
    => (forall a. g a -> m)
    -> Prod f g as
    -> m
foldMapProd f = ifoldMapProd (const f)

-- | 'foldMapUni' but with access to the index.
ifoldMapSing
    :: forall f k (as :: f k) m. (FProd f, Monoid m)
    => (forall a. Elem f as a -> Sing a -> m)
    -> Sing as
    -> m
ifoldMapSing f = ifoldMapProd f . singProd

-- | A 'foldMap' over all items in a collection.
foldMapSing
    :: forall f k (as :: f k) m. (FProd f, Monoid m)
    => (forall (a :: k). Sing a -> m)
    -> Sing as
    -> m
foldMapSing f = ifoldMapSing (const f)

-- | Witness an item in a type-level list by providing its index.
data Index :: [k] -> k -> Type where
    IZ :: Index (a ': as) a
    IS :: Index bs a -> Index (b ': bs) a

deriving instance Show (Index as a)

-- | Kind-indexed singleton for 'Index'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIndex'',
-- which has an actual proper 'Sing' instance.
data SIndex as a :: Index as a -> Type where
    SIZ :: SIndex (a ': as) a 'IZ
    SIS :: SIndex bs a i -> SIndex (b ': bs) a ('IS i)

deriving instance Show (SIndex as a i)

newtype instance Sing (i :: Index as a) where
    SIndex' :: SIndex as a i -> Sing i

instance SingI 'IZ where
    sing = SIndex' SIZ

instance SingI i => SingI ('IS i) where
    sing = case sing of
      SIndex' i -> SIndex' (SIS i)

instance SingKind (Index as a) where
    type Demote (Index as a) = Index as a
    fromSing (SIndex' i) = go i
      where
        go :: SIndex bs b i -> Index bs b
        go = \case
          SIZ   -> IZ
          SIS j -> IS (go j)
    toSing i = go i (SomeSing . SIndex')
      where
        go :: Index bs b -> (forall i. SIndex bs b i -> r) -> r
        go = \case
          IZ   -> ($ SIZ)
          IS j -> \f -> go j (f . SIS)

instance SDecide (Index as a) where
    SIndex' i %~ SIndex' j = go i j
      where
        go :: SIndex bs b i -> SIndex bs b j -> Decision (i :~: j)
        go = \case
          SIZ -> \case
            SIZ   -> Proved Refl
            SIS _ -> Disproved $ \case {}
          SIS i' -> \case
            SIZ   -> Disproved $ \case {}
            SIS j' -> case go i' j' of
              Proved Refl -> Proved Refl
              Disproved v -> Disproved $ \case Refl -> v Refl

instance FProd [] where
    type Elem [] = Index
    type Prod [] = Rec

    singProd = \case
      SNil         -> RNil
      x `SCons` xs -> x :& singProd xs

    traverseProd
        :: forall g h m as. Applicative m
        => (forall a. g a -> m (h a))
        -> Prod [] g as
        -> m (Prod [] h as)
    traverseProd f = go
      where
        go :: Prod [] g bs -> m (Prod [] h bs)
        go = \case
          RNil    -> pure RNil
          x :& xs -> (:&) <$> f x <*> go xs

    zipWithProd
        :: forall g h j as. ()
        => (forall a. g a -> h a -> j a)
        -> Prod [] g as
        -> Prod [] h as
        -> Prod [] j as
    zipWithProd f = go
      where
        go :: Prod [] g bs -> Prod [] h bs -> Prod [] j bs
        go = \case
          RNil -> \case
            RNil -> RNil
          x :& xs -> \case
            y :& ys -> f x y :& go xs ys

    htraverse
        :: forall ff g h as m. Applicative m
        => Sing ff
        -> (forall a. g a -> m (h (ff @@ a)))
        -> Prod [] g as
        -> m (Prod [] h (Fmap ff as))
    htraverse _ f = go
      where
        go :: Prod [] g bs -> m (Prod [] h (Fmap ff bs))
        go = \case
          RNil    -> pure RNil
          x :& xs -> (:&) <$> f x <*> go xs

    withIndices = \case
        RNil    -> RNil
        x :& xs -> (IZ :*: x) :& mapProd (\(i :*: y) -> IS i :*: y) (withIndices xs)

    ixProd
        :: forall g as a. ()
        => Elem [] as a
        -> Lens' (Prod [] g as) (g a)
    ixProd i0 (f :: g a -> h (g a)) = go i0
      where
        go :: Elem [] bs a -> Prod [] g bs -> h (Prod [] g bs)
        go = \case
          IZ -> \case
            x :& xs -> (:& xs) <$> f x
          IS i -> \case
            x :& xs -> (x :&) <$> go i xs

    toRec = id

instance RecApplicative as => PureProd [] as where
    pureProd = rpure

instance RPureConstrained c as => PureProdC [] c as where
    pureProdC = rpureConstrained @c

instance ReifyConstraint c f as => ReifyConstraintProd [] c f as where
    reifyConstraintProd = reifyConstraint @c

-- | Witness an item in a type-level 'Maybe' by proving the 'Maybe' is
-- 'Just'.
data IJust :: Maybe k -> k -> Type where
    IJust :: IJust ('Just a) a

deriving instance Show (IJust as a)

-- | Kind-indexed singleton for 'IJust'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIJust'',
-- which has an actual proper 'Sing' instance.
--
-- This distinction will be unnecessary once 'Sing' is a type family.
data SIJust as a :: IJust as a -> Type where
    SIJust :: SIJust ('Just a) a 'IJust

deriving instance Show (SIJust as a i)

newtype instance Sing (i :: IJust as a) where
    SIJust' :: SIJust as a i -> Sing i

instance SingI 'IJust where
    sing = SIJust' SIJust

instance SingKind (IJust as a) where
    type Demote (IJust as a) = IJust as a
    fromSing (SIJust' SIJust) = IJust
    toSing IJust = SomeSing (SIJust' SIJust)

instance SDecide (IJust as a) where
    SIJust' SIJust %~ SIJust' SIJust = Proved Refl

data PMaybe :: (k -> Type) -> Maybe k -> Type where
    PNothing :: PMaybe f 'Nothing
    PJust    :: f a -> PMaybe f ('Just a)

instance ReifyConstraintProd Maybe Show f as => Show (PMaybe f as) where
    showsPrec d xs = case reifyConstraintProd @_ @Show xs of
      PNothing                   -> showString "PNothing"
      PJust (V.Compose (Dict x)) -> showsUnaryWith showsPrec "PJust" d x

instance FProd Maybe where
    type instance Elem Maybe = IJust
    type instance Prod Maybe = PMaybe

    singProd = \case
      SNothing -> PNothing
      SJust x  -> PJust x
    withIndices = \case
      PNothing -> PNothing
      PJust x  -> PJust (IJust :*: x)
    traverseProd f = \case
      PNothing -> pure PNothing
      PJust x  -> PJust <$> f x
    zipWithProd f = \case
      PNothing -> \case
        PNothing -> PNothing
      PJust x -> \case
        PJust y -> PJust (f x y)
    htraverse _ f = \case
      PNothing -> pure PNothing
      PJust x  -> PJust <$> f x
    ixProd = \case
      IJust -> \f -> \case
        PJust x -> PJust <$> f x
    toRec = \case
      PNothing -> RNil
      PJust x  -> x :& RNil

instance PureProd Maybe 'Nothing where
    pureProd _ = PNothing
instance PureProd Maybe ('Just a) where
    pureProd x = PJust x

instance PureProdC Maybe c 'Nothing where
    pureProdC _ = PNothing
instance c a => PureProdC Maybe c ('Just a) where
    pureProdC x = PJust x

instance ReifyConstraintProd Maybe c g 'Nothing where
    reifyConstraintProd PNothing = PNothing
instance c (g a) => ReifyConstraintProd Maybe c g ('Just a) where
    reifyConstraintProd (PJust x) = PJust (V.Compose (Dict x))

-- | Witness an item in a type-level @'Either' j@ by proving the 'Either'
-- is 'Right'.
data IRight :: Either j k -> k -> Type where
    IRight :: IRight ('Right a) a

deriving instance Show (IRight as a)

-- | Kind-indexed singleton for 'IRight'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIRight'',
-- which has an actual proper 'Sing' instance.
data SIRight as a :: IRight as a -> Type where
    SIRight :: SIRight ('Right a) a 'IRight

deriving instance Show (SIRight as a i)

newtype instance Sing (i :: IRight as a) where
    SIRight' :: SIRight as a i -> Sing i

instance SingI 'IRight where
    sing = SIRight' SIRight

instance SingKind (IRight as a) where
    type Demote (IRight as a) = IRight as a
    fromSing (SIRight' SIRight) = IRight
    toSing IRight = SomeSing (SIRight' SIRight)

instance SDecide (IRight as a) where
    SIRight' SIRight %~ SIRight' SIRight = Proved Refl

data PEither :: (k -> Type) -> Either j k -> Type where
    PLeft  :: PEither f ('Left e)
    PRight :: f a -> PEither f ('Right a)

instance ReifyConstraintProd (Either j) Show f as => Show (PEither f as) where
    showsPrec d xs = case reifyConstraintProd @_ @Show xs of
      PLeft                       -> showString "PLeft"
      PRight (V.Compose (Dict x)) -> showsUnaryWith showsPrec "PRight" d x

instance FProd (Either j) where
    type instance Elem (Either j) = IRight
    type instance Prod (Either j) = PEither

    singProd = \case
      SLeft  _ -> PLeft
      SRight x -> PRight x
    withIndices = \case
      PLeft    -> PLeft
      PRight x -> PRight (IRight :*: x)
    traverseProd f = \case
      PLeft    -> pure PLeft
      PRight x -> PRight <$> f x
    zipWithProd f = \case
      PLeft -> \case
        PLeft -> PLeft
      PRight x -> \case
        PRight y -> PRight (f x y)
    htraverse _ f = \case
      PLeft    -> pure PLeft
      PRight x -> PRight <$> f x
    ixProd = \case
      IRight -> \f -> \case
        PRight x -> PRight <$> f x
    toRec = \case
      PLeft    -> RNil
      PRight x -> x :& RNil

instance PureProd (Either j) ('Left e) where
    pureProd _ = PLeft
instance PureProd (Either j) ('Right a) where
    pureProd x = PRight x

instance PureProdC (Either j) c ('Left e) where
    pureProdC _ = PLeft
instance c a => PureProdC (Either j) c ('Right a) where
    pureProdC x = PRight x

instance ReifyConstraintProd (Either j) c g ('Left e) where
    reifyConstraintProd PLeft = PLeft
instance c (g a) => ReifyConstraintProd (Either j) c g ('Right a) where
    reifyConstraintProd (PRight x) = PRight (V.Compose (Dict x))

-- | Witness an item in a type-level 'NonEmpty' by either indicating that
-- it is the "head", or by providing an index in the "tail".
data NEIndex :: NonEmpty k -> k -> Type where
    NEHead :: NEIndex (a ':| as) a
    NETail :: Index as a -> NEIndex (b ':| as) a

deriving instance Show (NEIndex as a)

-- | Kind-indexed singleton for 'NEIndex'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper
-- 'SNEIndex'', which has an actual proper 'Sing' instance.
data SNEIndex as a :: NEIndex as a -> Type where
    SNEHead :: SNEIndex (a ':| as) a 'NEHead
    SNETail :: SIndex as a i -> SNEIndex (b ':| as) a ('NETail i)

deriving instance Show (SNEIndex as a i)

newtype instance Sing (i :: NEIndex as a) where
    SNEIndex' :: SNEIndex as a i -> Sing i

instance SingI 'NEHead where
    sing = SNEIndex' SNEHead

instance SingI i => SingI ('NETail i) where
    sing = case sing of
      SIndex' i -> SNEIndex' (SNETail i)

instance SingKind (NEIndex as a) where
    type Demote (NEIndex as a) = NEIndex as a
    fromSing = \case
      SNEIndex' SNEHead     -> NEHead
      SNEIndex' (SNETail i) -> NETail $ fromSing (SIndex' i)
    toSing = \case
      NEHead   -> SomeSing (SNEIndex' SNEHead)
      NETail i -> withSomeSing i $ \case
        SIndex' j -> SomeSing (SNEIndex' (SNETail j))

instance SDecide (NEIndex as a) where
    (%~) = \case
      SNEIndex' SNEHead -> \case
        SNEIndex' SNEHead     -> Proved Refl
        SNEIndex' (SNETail _) -> Disproved $ \case {}
      SNEIndex' (SNETail i) -> \case
        SNEIndex' SNEHead -> Disproved $ \case {}
        SNEIndex' (SNETail j) -> case SIndex' i %~ SIndex' j of
          Proved Refl -> Proved Refl
          Disproved v -> Disproved $ \case Refl -> v Refl

data NERec :: (k -> Type) -> NonEmpty k -> Type where
    (:&|) :: f a -> Rec f as -> NERec f (a ':| as)
infixr 5 :&|

deriving instance (Show (f a), RMap as, ReifyConstraint Show f as, RecordToList as) => Show (NERec f (a ':| as))

instance FProd NonEmpty where
    type instance Elem NonEmpty = NEIndex
    type instance Prod NonEmpty = NERec

    singProd (x NE.:%| xs) = x :&| singProd xs
    withIndices (x :&| xs) =
          (NEHead :*: x)
      :&| mapProd (\(i :*: y) -> NETail i :*: y) (withIndices xs)
    traverseProd f (x :&| xs) =
        (:&|) <$> f x <*> traverseProd f xs
    zipWithProd f (x :&| xs) (y :&| ys) = f x y :&| zipWithProd f xs ys
    htraverse ff f (x :&| xs) =
        (:&|) <$> f x <*> htraverse ff f xs
    ixProd = \case
      NEHead -> \f -> \case
        x :&| xs -> (:&| xs) <$> f x
      NETail i -> \f -> \case
        x :&| xs -> (x :&|) <$> ixProd i f xs
    toRec (x :&| xs) = x :& xs

instance RecApplicative as => PureProd NonEmpty (a ':| as) where
    pureProd x = x :&| pureProd x

instance (c a, RPureConstrained c as) => PureProdC NonEmpty c (a ':| as) where
    pureProdC x = x :&| pureProdC @_ @c x

instance (c (g a), ReifyConstraint c g as) => ReifyConstraintProd NonEmpty c g (a ':| as) where
    reifyConstraintProd (x :&| xs) = V.Compose (Dict x)
                                 :&| reifyConstraintProd @_ @c xs

-- | Test if two indices point to the same item in a list.
--
-- We have to return a 'Maybe' here instead of a 'Decision', because it
-- might be the case that the same item might be duplicated in a list.
-- Therefore, even if two indices are different, we cannot prove that the
-- values they point to are different.
sameIndexVal
    :: Index as a
    -> Index as b
    -> Maybe (a :~: b)
sameIndexVal = \case
    IZ -> \case
      IZ   -> Just Refl
      IS _ -> Nothing
    IS i -> \case
      IZ   -> Nothing
      IS j -> sameIndexVal i j <&> \case Refl -> Refl


-- | Test if two indices point to the same item in a non-empty list.
--
-- We have to return a 'Maybe' here instead of a 'Decision', because it
-- might be the case that the same item might be duplicated in a list.
-- Therefore, even if two indices are different, we cannot prove that the
-- values they point to are different.
sameNEIndexVal
    :: NEIndex as a
    -> NEIndex as b
    -> Maybe (a :~: b)
sameNEIndexVal = \case
    NEHead -> \case
      NEHead   -> Just Refl
      NETail _ -> Nothing
    NETail i -> \case
      NEHead   -> Nothing
      NETail j -> sameIndexVal i j <&> \case Refl -> Refl

-- | Trivially witness an item in the second field of a type-level tuple.
data ISnd :: (j, k) -> k -> Type where
    ISnd :: ISnd '(a, b) b

deriving instance Show (ISnd as a)

-- | Kind-indexed singleton for 'ISnd'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SISnd'',
-- which has an actual proper 'Sing' instance.
data SISnd as a :: ISnd as a -> Type where
    SISnd :: SISnd '(a, b) b 'ISnd

deriving instance Show (SISnd as a i)

newtype instance Sing (i :: ISnd as a) where
    SISnd' :: SISnd as a i -> Sing i

instance SingI 'ISnd where
    sing = SISnd' SISnd

instance SingKind (ISnd as a) where
    type Demote (ISnd as a) = ISnd as a
    fromSing (SISnd' SISnd) = ISnd
    toSing ISnd = SomeSing (SISnd' SISnd)

instance SDecide (ISnd as a) where
    SISnd' SISnd %~ SISnd' SISnd = Proved Refl

data PTup :: (k -> Type) -> (j, k) -> Type where
    PSnd :: f a -> PTup f '(w, a)

deriving instance Show (f a) => Show (PTup f '(w, a))

instance FProd ((,) j) where
    type instance Elem ((,) j) = ISnd
    type instance Prod ((,) j) = PTup

    singProd (STuple2 _ x) = PSnd x
    withIndices (PSnd x) = PSnd (ISnd :*: x)
    traverseProd f (PSnd x) = PSnd <$> f x
    zipWithProd f (PSnd x) (PSnd y) = PSnd (f x y)
    htraverse _ f (PSnd x) = PSnd <$> f x
    ixProd ISnd f (PSnd x) = PSnd <$> f x
    toRec (PSnd x) = x :& RNil

instance PureProd ((,) j) '(w, a) where
    pureProd x = PSnd x

instance c a => PureProdC ((,) j) c '(w, a) where
    pureProdC x = PSnd x

instance c (g a) => ReifyConstraintProd ((,) j) c g '(w, a) where
    reifyConstraintProd (PSnd x) = PSnd $ V.Compose (Dict x)

-- | Trivially witness the item held in an 'Identity'.
--
-- @since 0.1.3.0
data IIdentity :: Identity k -> k -> Type where
    IId :: IIdentity ('Identity x) x

deriving instance Show (IIdentity as a)

-- | Kind-indexed singleton for 'IIdentity'.  Provided as a separate data
-- declaration to allow you to use these at the type level.  However, the
-- main interface is still provided through the newtype wrapper 'SIIdentity'',
-- which has an actual proper 'Sing' instance.
--
-- @since 0.1.5.0
data SIIdentity as a :: IIdentity as a -> Type where
    SIId :: SIIdentity ('Identity a) a 'IId

deriving instance Show (SIIdentity as a i)

newtype instance Sing (i :: IIdentity as a) where
    SIIdentity' :: SIIdentity as a i -> Sing i

instance SingI 'IId where
    sing = SIIdentity' SIId

instance SingKind (IIdentity as a) where
    type Demote (IIdentity as a) = IIdentity as a
    fromSing (SIIdentity' SIId) = IId
    toSing IId = SomeSing (SIIdentity' SIId)

instance SDecide (IIdentity as a) where
    SIIdentity' SIId %~ SIIdentity' SIId = Proved Refl

data PIdentity :: (k -> Type) -> Identity k -> Type where
    PIdentity :: f a -> PIdentity f ('Identity a)

deriving instance Show (f a) => Show (PIdentity f ('Identity a))

instance FProd Identity where
    type Elem Identity = IIdentity
    type Prod Identity = PIdentity

    singProd (SIdentity x) = PIdentity x
    withIndices (PIdentity x) = PIdentity (IId :*: x)
    traverseProd f (PIdentity x) = PIdentity <$> f x
    zipWithProd f (PIdentity x) (PIdentity y) = PIdentity (f x y)
    htraverse _ f (PIdentity x) = PIdentity <$> f x
    ixProd IId f (PIdentity x) = PIdentity <$> f x
    toRec (PIdentity x) = x :& RNil

instance PureProd Identity ('Identity a) where
    pureProd x = PIdentity x

instance c a => PureProdC Identity c ('Identity a) where
    pureProdC x = PIdentity x

instance c (g a) => ReifyConstraintProd Identity c g ('Identity a) where
    reifyConstraintProd (PIdentity x) = PIdentity $ V.Compose (Dict x)
