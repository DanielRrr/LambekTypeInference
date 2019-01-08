module Rules where

open import Types
open import Expression

open import Data.Nat
open import Data.Product
open import Data.Vec

data TypeEnv : Set where
    typeEnv : ∀ {n} → Vec (Name × TVar) n → TypeEnv  

data TypeSubst : Set where
    typeSubst : ∀ {n} → Vec (TVar × Type) n → TypeSubst
