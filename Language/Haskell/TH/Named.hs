module Language.Haskell.TH.Named (Named(..)) where

import Language.Haskell.TH.Syntax



-- | This is semantically murky: it's just the name of anything that
-- \"naturally\" /defines/ a name; error if it doesn't.
class Named t where name_of :: t -> Name

instance Named Info where
  name_of i = case i of
    ClassI d _ -> name_of d
    ClassOpI n _ _ _ -> n
    TyConI d -> name_of d
    PrimTyConI n _ _ -> n
    DataConI n _ _ _ -> n
    VarI n _ _ _ -> n
    TyVarI n _ -> n

instance Named TyVarBndr where
  name_of (PlainTV n) = n
  name_of (KindedTV n _) = n

instance Named Dec where
  name_of d = case d of
    FunD n _ -> n
    ValD p _ _ -> name_of p
    DataD _ n _ _ _ -> n
    NewtypeD _ n _ _ _ -> n
    TySynD n _ _ -> n
    ClassD _ n _ _ _ -> n
    FamilyD _ n _ _ -> n
    o -> error $ show o ++ " is not a named declaration."

instance Named Con where
  name_of c = case c of
    NormalC n _ -> n
    RecC n _ -> n
    InfixC _ n _ -> n
    ForallC _ _ c -> name_of c

instance Named Pat where
  name_of p = case p of
    VarP n -> n
    AsP n _ -> n
    SigP p _ -> name_of p
    o -> error $ "The pattern `" ++ show o ++ "' does not define exactly one name."
