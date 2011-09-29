{-# LANGUAGE FlexibleContexts, TypeOperators, TemplateHaskell, ViewPatterns,
  FlexibleInstances, UndecidableInstances, RankNTypes #-}

{-# OPTIONS_GHC -fcontext-stack=23 #-}

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{- |

Substution, free variables, and alpha-equivalence for the Template Haskell AST.

@forall x y iso. global_alpha x y => alpha x y iso@

> d0 = data Maybe a = Nothing | Just a
> d1 = data Maybe x = Nothing | Just x
> d2 = data Option x = None | Some x
> d3 = data Option x = Some x | None
> 
> global_alpha d0 d1 = True
> forall iso. alpha d0 d2 iso = True
> forall d iso. d `elem` [d0, d1, d2, d3] => alpha d d3 iso = False

-}

module Language.Haskell.TH.Substitution
  (alpha, global_alpha, binders, free, subst, Sub(..)) where

import Language.Haskell.TH.Named

import Language.Haskell.TH.Generics
import Language.Haskell.TH
import qualified Language.Haskell.TH

import Generics.Deriving.TH.Case

import Data.Map (Map)
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Map as Map
import Data.Traversable (forM)

import Data.Char (isUpper)





-------------------- generic
class Free t where
  free :: t -> [Either Name Name]
class Free1 t where
  free1 :: t p -> [Either Name Name]

gfree :: (Generic t, Free1 (Rep t)) => t -> [Either Name Name]
gfree = free1 . from

instance Free1 V1 where
  free1 _ = error "Language.Haskell.Substitution.free1 void"
instance Free1 U1 where free1 _ = []
instance Free c => Free1 (K1 i c) where
  free1 (K1 c) = free c
instance Free1 t => Free1 (M1 i c t) where
  free1 (M1 t) = free1 t
instance (Free1 l, Free1 r) => Free1 (l :+: r) where
  free1 (L1 t) = free1 t
  free1 (R1 t) = free1 t
instance (Free1 l, Free1 r) => Free1 (l :*: r) where
  free1 (l :*: r) = free1 l ++ free1 r

fmap concat $ forM [''Kind, ''Int] $
   \(conT -> t) -> [d| instance Free $t where free _ = [] |] 

instance Free a => Free [a] where
  free = concatMap free
instance Free a => Free (Maybe a) where
  free = maybe [] free

instance Free Pred where
  free (ClassP n tys) = Left n : free tys
  free (EqualP ty1 ty2) = free ty1 ++ free ty2



-------------------- generic
class Binders t where
  binders :: t -> [Either Name (Maybe Name)]
class Binders1 t where
  binders1 :: t p -> [Either Name (Maybe Name)]

gbinders :: (Generic t, Binders1 (Rep t)) => t -> [Either Name (Maybe Name)]
gbinders = binders1 . from


--------------------
instance Free Type where
  free = $(let q = varE 'free in gd_case [
    [| \(ForallT tvbs c ty) ->
       filter (`notElem` mapMaybe (either (Just . Left) (fmap Right)) ($(varE 'binders) tvbs)) $
                $q c ++ $q ty |],
    [| \(VarT n) -> [Left n] |],
    [| \(ConT n) -> [Left n] |]
               ] (const [| free1 |]))

close_ :: Binders a => a -> [Either Name Name] -> [Either Name Name]
close_ a b = filter (either (p . Left) (p . Right . Just)) b where
  bs = binders a
  p = (`elem` bs)

close' :: (Binders a, Free a) => a -> [Either Name Name] -> [Either Name Name]
close' a b = free a ++ close_ a b

closes x = foldr close' [] x
close a b = close' a (free b)

newtype Cascade a = Cascade [a]
instance (Free a, Binders a) => Free (Cascade a) where
  free (Cascade xs) = closes xs
instance Binders a => Binders (Cascade a) where
  binders (Cascade xs) = gbinders xs

instance Free Range where free = gfree

instance Free Clause where free (Clause p b ds) = close' p (close ds b)

instance Free TyVarBndr where free _ = []

instance Free Con where
  free (NormalC _ sts) = free $ map snd sts
  free (RecC _ sts) = free $ map (\(_, _, ty) -> ty) sts
  free (InfixC (_, ty1) _ (_, ty2)) = free ty1 ++ free ty2
  free (ForallC tvbs c con) = close' tvbs $ close (BTV c) con

instance Free FunDep where free (FunDep ns ms) = map Left (ns ++ ms)
instance Free Pragma where
  free (InlineP n _) = [Right n]
  free (SpecialiseP n ty _) = Right n : free ty

instance Free Dec where
  free d = case d of
    FunD n cls -> close_ (BN [Right (Just n)]) (free cls)
    ValD p b ds -> close' p (close ds b)
    DataD c n tvbs cons ns ->
      (map Left ns ++) $ close_ (BN [Left n]) $ close' tvbs $
                         close (BTV c) cons
    NewtypeD c n tvbs con ns -> free (DataD c n tvbs [con] ns)
    TySynD n tvbs ty -> close tvbs ty
    ClassD c n tvbs fds ds ->
      close_ (BN [Left n]) $ close' tvbs $ (free fds ++) $ close (BTV c) ds
    InstanceD c ty ds -> close' (BTV ty) $ close (BTV c) ds
    SigD _ ty -> free ty
    ForeignD f -> case f of
      ImportF _ _ _ _ ty -> free ty
      ExportF _ _ n ty -> Right n : free ty
    PragmaD p -> free p
    FamilyD {} -> []
    DataInstD c _ tys cons ns ->
      (map Left ns ++) $ close' (BTV tys) $ close (BTV c) cons
    NewtypeInstD c n tys con ns -> free (DataInstD c n tys [con] ns)
    TySynInstD _ tys ty -> close (BTV tys) ty


instance Free Pat where
  free = $(let qc = varE 'close; qcs = varE 'closes; q = varE 'free in gd_case [
    [| \(LitP _) -> [] |],
    [| \(VarP _) -> [] |],
    [| \(TupP ps) -> $qcs ps |],
    [| \(ConP n ps) -> Right n : $qcs ps |],
    [| \(InfixP p1 n p2) -> Right n : $qc p1 p2 |],
    [| \(AsP n p) -> $q p |],
    [| \(RecP n fes) -> Right n : map (Right . fst) fes ++ $qcs (map snd fes) |],
    [| \(ListP ps) -> $qcs ps |]
           ] (const [| free1 |]))
  

instance Free Exp where
  free = $(let qc = varE 'close; q = varE 'free in gd_case [
    [| \(VarE n) -> [Right n] |],
    [| \(ConE n) -> [Right n] |],
    [| \(LitE _) -> [] |],
    [| \(LamE ps e) -> $qc (Cascade ps) e |],
    [| \(LetE ds e) -> $qc ds e |],
    [| \(RecConE n fes) -> Right n : map (Right . fst) fes ++ $q (map snd fes) |],
    [| \(RecUpdE e fes) -> $q e ++ map (Right . fst) fes ++ $q (map snd fes) |]
           ] (const [| free1 |]))

instance Free Stmt where
  free (BindS p e) = close p e
  free (LetS ds) = foldr close' [] ds
  free (NoBindS e) = free e
  free (ParS stss) = concatMap (foldr close' []) stss
instance Free Guard where
  free (NormalG e) = free e
  free (PatG sts) = foldr close' [] sts
instance Free Body where
  free (GuardedB ges) = concatMap (uncurry close) ges
  free (NormalB e) = free e
instance Free Match where
  free (Match p b ds) = close' p $ close ds b

instance Free ClassInstance where
  free (ClassInstance dfun tvbs cxt cls tys) =
    ([Right dfun, Left cls] ++) $ close' tvbs $ close (BTV cxt) tys


--------------------
b2i :: (Binders a, Subst a) => a -> a -> (Iso -> Bool) -> Iso -> Bool
b2i x y k = w (binders x) (binders y) where
  w  [] [] = alpha x y `andI` k
  w (Left l : ls) (Left r : rs) = w ls rs . (addI l r)
  w (Right (Just l) : ls) (Right (Just r) : rs) = w ls rs . (addI l r)
  w (Right _ : ls) (Right _ : rs) = w ls rs
  w _ _ = const False

cascadeI :: (Binders a, Subst a) => [a] -> [a] -> Iso -> Bool
cascadeI = w where
  w [] [] = trueI
  w (l : ls) (r : rs) = b2i l r $ w ls rs
  w _ _ = const False

listI :: [a] -> [b] -> (a -> b -> Iso -> Bool) -> (Iso -> Bool) -> Iso -> Bool
listI x y f k = w x y where
  w [] [] = k
  w (l : ls) (r : rs) = f l r `andI` w ls rs
  w _ _ = const False

data BN = BN [Either Name (Maybe Name)]
instance Binders BN where binders (BN x) = x
instance Subst BN where
  subst sub (BN x) = BN $ map (either (Left . r) (Right . fmap r)) x where
    r = subst sub
  alpha (BN l) (BN r) = listI l r each trueI where
    each (Left l) (Left r) = alpha l r
    each (Right l) (Right r) = alpha l r
    each _ _ = falseI

freeTVs :: Free a => a -> [Either Name (Maybe Name)]
freeTVs = binders . BTV

newtype BTV a = BTV a
instance Free a => Free (BTV a) where
  free (BTV a) = free a
instance Free a => Binders (BTV a) where
  binders (BTV p) = map (either Left (Right . Just)) $ fvars $ free p
    where fvars x = filter (either p (const False)) x where
            p n = not (isUpper c || ':' == c) where
              c = head (nameBase n)
instance Subst a => Subst (BTV a) where
  subst sub (BTV x) = BTV (subst sub x)
  alpha (BTV l) (BTV r) = alpha l r

newtype BTC a = BTC a
instance Free a => Binders (BTC a) where
  binders (BTC p) = map (either Left (Right . Just)) $ fvars $ free p
    where fvars x = filter (either p (const False)) x where
            p n = isUpper c || ':' == c where
              c = head (nameBase n)
instance Subst a => Subst (BTC a) where
  subst sub (BTC x) = BTC (subst sub x)
  alpha (BTC l) (BTC r) = alpha l r

-------------------- generic instances
instance Binders1 V1 where
  binders1 _ = error "Language.Haskell.Substitution.binders1 void"
instance Binders1 U1 where binders1 _ = []
instance Binders c => Binders1 (K1 i c) where
  binders1 (K1 c) = binders c
instance Binders1 t => Binders1 (M1 i c t) where
  binders1 (M1 t) = binders1 t
instance (Binders1 l, Binders1 r) => Binders1 (l :+: r) where
  binders1 (L1 t) = binders1 t
  binders1 (R1 t) = binders1 t
instance (Binders1 l, Binders1 r) => Binders1 (l :*: r) where
  binders1 (l :*: r) = binders1 l ++ binders1 r




instance Binders Pat where
  binders = $(let q = varE 'binders in gd_case [
    [| \(LitP _) -> [] |],
    [| \(VarP n) -> [Right (Just n)] |],
    [| \(ConP _ pats) -> $q pats |],
    [| \(InfixP p1 _ p2) -> $q p1 ++ $q p2 |],
    [| \(AsP n pat) -> Right (Just n) : $q pat |],
    [| \WildP -> [Right Nothing] |],
    [| \(RecP _ fps) -> $q (map snd fps) |],
    [| \(SigP pat ty) -> $q pat ++ $q (BTV ty) |],
    [| \(ViewP _ pat) -> $q pat |]
                      ] (const [| binders1 |]))

instance Binders Dec where
  binders (FunD n _) = [Right (Just n)]
  binders (ValD p _ _) = binders p
  binders (DataD _ n _ cons _) = Right (Just n) : binders cons
  binders (NewtypeD _ n _ con _) = Right (Just n) : binders con
  binders (TySynD n _ _) = [Right (Just n)]
  binders (ClassD _ n _ _ ds) = Right (Just n) : binders ds
  binders InstanceD{} = []
  binders (SigD n _) = [Right (Just n)]
  binders (ForeignD f) = case f of
    ImportF _ _ _ n _ -> [Right (Just n)]
    ExportF{} -> []
  binders (PragmaD _) = []
  binders (FamilyD _ n _ _) = [Right (Just n)]
  binders (DataInstD _ n _ cons _) = Right (Just n) : binders cons
  binders (NewtypeInstD _ n _ con _) = Right (Just n) : binders con
  binders TySynInstD{} = []

instance Binders Con where
  binders (NormalC n _) = [Right (Just n)]
  binders (RecC n vsts) = map (Right . Just) $ n : map (\(n, _, _) -> n) vsts
  binders (InfixC _ n _) = [Right (Just n)]
  binders (ForallC tvbs _ con) = binders con

instance Binders TyVarBndr where
  binders = (:[]) . Left . name_of

instance Binders Stmt where
  binders (BindS pat _) = binders pat
  binders (LetS ds) = binders ds
  binders (NoBindS _) = []
  binders (ParS stss) = binders stss

instance Binders Guard where
  binders (NormalG _) = []
  binders (PatG sts) = binders sts

instance Binders a => Binders [a] where
  binders = concatMap binders



--------------------
-- the first map captures binders too
data Sub = Sub (Map Name Name) (Map Name Type) (Map Name Exp)

less :: Binders a => Sub -> a -> Sub
less (Sub ns ts es) nms = Sub ns (f False ts) (f True es) where
  f b m = Map.difference m nms' where
    nms' = Map.fromList $ zip
             (mapMaybe (if b then either no id else either Just no) $ binders nms)
             (repeat ())
      where no _ = Nothing


type Iso = [(Name, Name)]
addI :: Name -> Name -> Iso -> Iso
addI l r iso = (l, r) : filter p iso where
  p (x, y) = not (x == l || y == r)

-------------------- generic transformation
class Subst t where
  subst :: Sub -> t -> t
  -- | alpha-equivalence; internally bound names, names bound by this value
  -- that are visible outside of it (e.g. Dec or Pat), and names paired in the
  -- third argument are considered indistinguishable
  alpha :: t -> t -> Iso -> Bool
class Subst1 t where
  subst1 :: Sub -> t p -> t p
  alpha1 :: t x -> t y -> Iso -> Bool

-- | @global_alpha@ requires the base names bound by the @t@s to also be
-- equivalent.
global_alpha :: (Binders t, Subst t) => t -> t -> Bool
global_alpha l r = alpha (BN $ bases $ binders l, l) (BN $ bases $ binders r, r) [] where
  bases = map (either (Left . f) (Right . fmap f)) where
    f = mkName . nameBase

sless :: (Binders a, Subst t) => Sub -> a -> t -> t
sless sub a = subst (sub `less` a)

newtype F = F (forall t. Subst t => t -> t)
mkF :: Sub -> F
mkF sub = F (subst sub)

newtype FL = FL (forall a t. (Binders a, Subst t) => a -> t -> t)
mkFLess :: Sub -> FL
mkFLess sub = FL (sless sub)

g :: (Generic t, Subst1 (Rep t)) => Sub -> t -> t
g sub = to . subst1 sub . from

galpha :: (Generic t, Subst1 (Rep t)) => t -> t -> Iso -> Bool
galpha x y = alpha1 (from x) (from y)

-------------------- generic instances
instance Subst1 V1 where
  subst1 _ _ = error "Language.Haskell.Substitution.subst1 void"
  alpha1 _ _ _ = error "Language.Haskell.Substitution.alpha1 void"
instance Subst1 U1 where
  subst1 _ _ = U1
  alpha1 _ _ _ = True
instance Subst c => Subst1 (K1 i c) where
  subst1 sub (K1 c) = K1 $ subst sub c
  alpha1 (K1 l) (K1 r) = alpha l r
instance Subst1 t => Subst1 (M1 i c t) where
  subst1 sub (M1 t) = M1 $ subst1 sub t
  alpha1 (M1 l) (M1 r) = alpha1 l r 
instance (Subst1 l, Subst1 r) => Subst1 (l :+: r) where
  subst1 sub (L1 t) = L1 $ subst1 sub t
  subst1 sub (R1 t) = R1 $ subst1 sub t
  alpha1 (L1 l) (L1 r) = alpha1 l r
  alpha1 (R1 l) (R1 r) = alpha1 l r
  alpha1 _ _ = const False
instance (Subst1 l, Subst1 r) => Subst1 (l :*: r) where
  subst1 sub (l :*: r) = subst1 sub l :*: subst1 sub r
  alpha1 (ll :*: lr) (rl :*: rr) = alpha1 ll rl `andI` alpha1 lr rr

andI f g iso = f iso && g iso
trueI = const True
falseI = const False

-------------------- short-circuits
fmap concat $ forM [''Bool, ''Int, ''Char, ''Kind, ''InlineSpec, ''Lit,
                    ''Strict, ''FamFlavour, ''Safety, ''Callconv,
                    ''Language.Haskell.TH.Fixity] $
   \(conT -> t) -> [d| instance Eq $t => Subst $t where subst _ = id; alpha x y _ = x == y |] 

-------------------- compositional
fmap concat $ forM [''Range, ''Pred, ''Con, ''TyVarBndr, ''Foreign, ''FunDep,
                    ''Pragma] $
   \(conT -> t) -> [d| instance Subst $t where subst = g; alpha = galpha |] 

instance (Subst a, Subst b) => Subst (a, b) where subst = g; alpha = galpha
instance (Subst a, Subst b, Subst c) => Subst (a, b, c) where subst = g; alpha = galpha
instance Subst a => Subst (Maybe a) where subst = g; alpha = galpha
instance Subst a => Subst [a] where subst = g; alpha = galpha

cascade :: (Binders a, Subst a) => Sub -> [a] -> [a]
cascade _ [] = []
cascade sub (a : as) = subst sub a : sless sub a as



instance Subst Name where
  subst (Sub ns _ _) n = fromMaybe n (Map.lookup n ns)
  alpha x y iso = (x, y) `elem` iso || x == y
 


instance Subst Type where
  subst sub@(Sub _ tys _) ty = case ty of
    ForallT tvbs cxt ty -> ForallT (r tvbs) (r' cxt) (r' ty)
      where F r' = mkF (sub `less` tvbs)
    VarT n -> fromMaybe (VarT (r n)) (Map.lookup n tys)
    _ -> g sub ty
    where F r = mkF sub
  alpha (ForallT ltvbs lcxt lty) (ForallT rtvbs rcxt rty) =
    b2i ltvbs rtvbs $ alpha (lcxt, lty) (rcxt, rty)
  alpha l r = galpha l r


instance Subst Exp where
  subst sub@(Sub _ _ es) e = case e of
    VarE n -> fromMaybe (VarE (r n)) (Map.lookup n es)
    LamE pats e -> LamE (r pats) (rl pats e)
    LetE ds e -> LetE (r ds) (rl  ds e)
    DoE sts -> DoE $ cascade sub sts
    CompE sts -> CompE $ cascade sub sts
    _ -> g sub e
    where F r = mkF sub; FL rl = mkFLess sub
  alpha (LamE lpats le) (LamE rpats re) = b2i lpats rpats $ alpha le re
  alpha (LetE lds le) (LetE rds re) = b2i lds rds $ alpha le re
  alpha (DoE lsts) (DoE rsts) = cascadeI lsts rsts
  alpha (CompE lsts) (CompE rsts) = cascadeI lsts rsts
  alpha l r = galpha l r

instance Subst Match where
  subst sub (Match p b ds) =
    Match (subst sub p) (sless sub' ds b) (subst sub' ds)
    where sub' = sub `less` p
  alpha (Match lp lb lds) (Match rp rb rds) =
    b2i lp rp $ b2i lds rds $ alpha lb rb
instance Subst Stmt where
  subst sub st = case st of
    BindS p e -> BindS (r p) (sless sub p e)
    LetS ds -> LetS (cascade sub ds)
    NoBindS _ -> r st
    ParS stss -> ParS $ map (cascade sub) stss
    where F r = mkF sub
  alpha (BindS lp le) (BindS rp re) = b2i lp rp $ alpha le re
  alpha (LetS lds) (LetS rds) = cascadeI lds rds
  alpha (ParS lstss) (ParS rstss) = listI lstss rstss cascadeI trueI
  alpha l r = galpha l r
    
instance Subst Body where
  subst sub b = case b of
    GuardedB ges -> GuardedB [ (r gu, sless sub gu e) | (gu, e) <- ges ]
    _ -> g sub b
    where F r = mkF sub
  alpha (GuardedB lges) (GuardedB rges) =
    listI lges rges (\(lg, le) (rg, re) -> b2i lg rg $ alpha le re) trueI
  alpha l r = galpha l r

instance Subst Guard where
  subst sub gu = case gu of
    PatG sts -> PatG (cascade sub sts)
    _ -> g sub gu
  alpha (PatG lsts) (PatG rsts) = cascadeI lsts rsts
  alpha l r = galpha l r

instance Subst Pat where
  subst sub p = case p of
    TupP ps -> TupP (cascade sub ps)
    ConP n ps -> ConP (r n) (cascade sub ps)
    InfixP p1 n p2 -> InfixP (r p1) (r n) (rl p1 p2)
    AsP n pat -> AsP (r n) (rl (VarP n) pat)
    RecP n fps -> RecP (r n) $ zip (map fst fps) (cascade sub (map snd fps))
    ListP pats -> ListP (cascade sub pats)
    _ -> g sub p
    where F r = mkF sub; FL rl = mkFLess sub
  alpha (TupP lps) (TupP rps) = cascadeI lps rps
  alpha (ConP ln lps) (ConP rn rps) = listI lps rps alpha $ alpha ln rn
  alpha (InfixP lp1 ln lp2) (InfixP rp1 rn rp2) =
    alpha ln rn `andI` (b2i lp1 rp1 $ alpha lp2 rp2)
  alpha (AsP ln lp) (AsP rn rp) = alpha ln rn `andI` alpha lp rp
  alpha (RecP ln lfps) (RecP rn rfps) =
    alpha ln rn `andI` cascadeI (map snd lfps) (map snd rfps)
  alpha (ListP lps) (ListP rps) = cascadeI lps rps
  alpha l r = galpha l r



instance Subst Dec where
  subst sub d = case d of
    FunD n cls -> FunD (r n) (sless sub (VarP n) cls)
    ValD p b ds -> ValD (r p) (sless sub' ds b) (subst sub' ds)
      where sub' = sub `less` p
    DataD c n tvbs cons ns ->
      DataD (rl tvbs c) (r n) (r tvbs) (rl tvbs cons) (r ns)
    NewtypeD c n tvbs con ns ->
      NewtypeD (rl tvbs c) (r n) (r tvbs) (rl tvbs con) (r ns)
    TySynD n tvbs ty -> TySynD (r n) (r tvbs) (rl tvbs ty)
    ClassD c n tvbs fds ds ->
      ClassD (rl tvbs c) (r n) (r tvbs) (rl tvbs fds) (rl tvbs ds)
    InstanceD c ty ds ->
      InstanceD (rl (BN tyns) c) (r ty) (rl (BN $ tyns ++ freeTVs c) ds)
      where tyns = freeTVs ty
    SigD n ty -> SigD (r n) (r ty)
    DataInstD c n tys cons ns ->
      DataInstD (rl (BN tyns) c) (r n) (r tys) (rl (BN $ tyns ++ freeTVs c) cons) (r ns)
      where tyns = freeTVs tys
    NewtypeInstD c n tys con ns ->
      NewtypeInstD (rl (BN tyns) c) (r n) (r tys) (rl (BN $ tyns ++ freeTVs c) con) (r ns)
      where tyns = freeTVs tys
    TySynInstD n tys ty -> TySynInstD (r n) (r tys) (rl (BTV tys) ty)
    _ -> g sub d
    where F r = mkF sub; FL rl = mkFLess sub
  alpha (FunD ln lcls) (FunD rn rcls) = b2i (VarP ln) (VarP rn) $ alpha lcls rcls
  alpha (ValD lp lb lds) (ValD rp rb rds) = b2i lp rp $ b2i lds rds $ alpha lb rb
  alpha (DataD lc ln ltvbs lcons lns) (DataD rc rn rtvbs rcons rns) =
    andI (alpha lns rns) $ b2i ltvbs rtvbs $ b2i (BN [Left ln]) (BN [Left rn]) $
         alpha lc rc `andI` b2i lcons rcons trueI
  alpha (NewtypeD lc ln ltvbs lcon lns) (NewtypeD rc rn rtvbs rcon rns) =
    alpha (DataD lc ln ltvbs [lcon] lns) (DataD rc rn rtvbs [rcon] rns)
  alpha (TySynD ln ltvbs lty) (TySynD rn rtvbs rty) =
    andI (alpha ln rn) $ b2i ltvbs rtvbs $ alpha lty rty
  alpha (ClassD lc ln ltvbs lfds lds) (ClassD rc rn rtvbs rfds rds) =
    b2i (BN [Left ln]) (BN [Left rn]) $ b2i ltvbs rtvbs $ andI (alpha lfds rfds) $
        b2i (BTV lc) (BTV rc) $ b2i lds rds trueI
  alpha (InstanceD lc lty lds) (InstanceD rc rty rds) =
    b2i (BTV lty) (BTV rty) $ b2i (BTV lc) (BTV rc) $ alpha lds rds
  alpha (DataInstD lc ln ltys lcons lns) (DataInstD rc rn rtys rcons rns) =
    andI (alpha lns rns) $ b2i (BTV ltys) (BTV rtys) $ b2i (BN [Left ln]) (BN [Left rn]) $
         alpha lc rc `andI` b2i lcons rcons trueI
  alpha (NewtypeInstD lc ln ltys lcon lns) (NewtypeInstD rc rn rtys rcon rns) =
    alpha (DataInstD lc ln ltys [lcon] lns) (DataInstD rc rn rtys [rcon] rns)
  alpha (TySynInstD ln ltys lty) (TySynInstD rn rtys rty) =
    andI (alpha ln rn) $ b2i (BTV ltys) (BTV rtys) $ alpha lty rty
  alpha l r = galpha l r

instance Subst Clause where
  subst sub (Clause ps b ds) =
    Clause (cascade sub ps) (sless sub' ds b) (subst sub' ds)
    where sub' = sub `less` ps
  alpha (Clause lps lb lds) (Clause rps rb rds) =
    b2i lps rps $ b2i lds rds $ alpha lb rb

instance Subst ClassInstance where
  subst sub (ClassInstance dfun tvs cxt cls tys) =
    ClassInstance (r dfun) (r tvs) (r cxt) (r cls) (r tys)
    where F r = mkF (sub `less` tvs)
  alpha (ClassInstance ldfun ltvs lcxt lcls ltys) (ClassInstance rdfun rtvs rcxt rcls rtys) =
    b2i ltvs rtvs $ alpha ldfun rdfun `andI` alpha lcxt rcxt `andI`
        alpha lcls rcls `andI` alpha ltys rtys
