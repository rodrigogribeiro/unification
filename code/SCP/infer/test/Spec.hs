import STLC
import Control.Monad
import Test.QuickCheck
import Data.Maybe
import qualified TypeInfer as Infer

-- some instances to be used by QuickCheck test generators

instance Arbitrary Nat where
  arbitrary
    = oneof [ return O
            , liftM S arbitrary ]

instance Arbitrary Ty where
  arbitrary
    = oneof [ return Con 
            , liftM2 Arr arbitrary arbitrary ]

-- checking if a type is inhabited, i.e. is an intuitionistic logic tautology

taut :: [Ty] -> Ty -> Bool
taut ctx (Arr l r) = taut (l : ctx) r
taut ctx t = atom ctx t

atom :: [Ty] -> Ty -> Bool
atom ctx t = try [] ctx
  where
    try js [] = False
    try js (h : hs) = from h t (js ++ hs) ||
                      try (h : js) hs

from :: Ty -> Ty -> [Ty] -> Bool
from Con  a ctx = a == Con
from (Arr l r) a ctx = from r a ctx && taut ctx l


-- generates only type correct terms

typeCorrect :: Gen Term
typeCorrect
  = do
      t <- suchThat arbitrary (taut [])
      genTerm [] t

genTerm :: Tyctx -> Ty -> Gen Term
genTerm [] Con = return Const_t
genTerm ctx Con
  = do
      let ctx' = [p | p <- ctx, Con == (snd p)]
      if null ctx' then return Const_t
         else liftM (Var_t . fst) (elements ctx')
genTerm ctx (Arr l r)
  = do
      v <- arbitrary :: Gen Nat
      liftM (Lam_t v) (genTerm ((v,l):ctx) r)

-- some isos

convertTy :: Infer.Ty -> Ty
convertTy Infer.Con = Con
convertTy (Infer.Var v) = Var (convertNat1 v)
convertTy (Infer.Arr l r) = Arr (convertTy l) (convertTy r)

convertNat1 :: Infer.Nat -> Nat
convertNat1 Infer.O = O
convertNat1 (Infer.S n) = S (convertNat1 n)

convertNat :: Nat -> Infer.Nat
convertNat O = Infer.O
convertNat (S n) = Infer.S (convertNat n)

convertTerm :: Term -> Infer.Term
convertTerm Const_t = Infer.Const_t
convertTerm (Var_t v) = Infer.Var_t (convertNat v)
convertTerm (Lam_t v t) = Infer.Lam_t (convertNat v) (convertTerm t)
convertTerm (App_t l r) = Infer.App_t (convertTerm l) (convertTerm r)

-- property for well typed terms

typeInferCorrect :: (Term -> Bool) -> Property
typeInferCorrect f = forAll typeCorrect f

-- running test suite

main :: IO ()
main = do
  verboseCheck (typeInferCorrect (isJust . type_infer))
  verboseCheck (typeInferCorrect (isJust . Infer.type_infer . convertTerm))
