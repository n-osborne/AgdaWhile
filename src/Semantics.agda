module Semantics where

-- could use :
-- open import Data.AVL.IndexedMap
open import Data.Maybe
open import Data.Nat
open import Data.Bool
open import Syntax

-- Define the store (environment) by a function

-- we need bool equality on Wvar
_==_ : Wvar → Wvar → Bool
(var n₁) == (var n₂) = n₁ ≡ᵇ n₂

-- the empty store
stempty : Wvar → Maybe Wdata
stempty _ = nothing

stupdate : Wvar → Wdata → (Wvar → Maybe Wdata) → Wvar → Maybe Wdata
stupdate v₁ d f v₂ with v₁ == v₂
... | true = just d
... | false = f v₂

stremove : Wvar → (Wvar → Maybe Wdata) → Wvar → Maybe Wdata
stremove v₁ f v₂ with v₁ == v₂
... | true = nothing
... | false = f v₂

