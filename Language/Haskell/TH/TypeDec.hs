{-# LANGUAGE ViewPatterns #-}

module Language.Haskell.TH.TypeDec (TyDec(..), project, projectQ, kind) where

import Language.Haskell.TH



data TyDec = TyDec Cxt Name [TyVarBndr] [Con]

project :: Dec -> Maybe TyDec
project (DataD c n tvbs cons _) = Just (TyDec c n tvbs cons)
project (NewtypeD c n tvbs con _) = Just (TyDec c n tvbs [con])
project _ = Nothing

projectQ :: String -> Name -> Q TyDec
projectQ s n = do
  i <- reify n
  case i of
    TyConI (project -> Just tyd) -> return tyd
    _ -> fail $ s ++ " expects the name of a data or newtype; " ++ show n ++ " is neither"



kind (TyDec _ _ tvbs _) = foldr cons StarK tvbs where
  cons (KindedTV _ k) = ArrowK k
  cons (PlainTV _) = ArrowK StarK
