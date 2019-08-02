module Semantics where
-- This module corresponds to the Section 2.2 of the book

open import IntermediaryRepresentation
open import Syntax
open import Data.List
open import Data.Bool


-- Small Step Semantic for While Language As a Function
oneStepEval : Wenv → Wenv
-- assignement
oneStepEval (record { st     = s ;
                      stack  = l ;
                      cmds   = s₁ ∣ (cmd@(n , (assign x y)) ∷ s₂) ;
                      output = o }) = record { st     = stupdate x (evalExp y s) s ;
                                               stack  = l ;
                                               cmds   = (cmd ∷ s₁) ∣ s₂ ;
                                               output = o }
-- enter while loop                             
oneStepEval (record { st     = s ;
                      stack  = l ;
                      cmds   = s₁ ∣ (cmd@(n , whileBegin) ∷ s₂) ;
                      output = o }) = record { st     = s ;
                                               stack  = n ∷ l ;
                                               cmds   = (cmd ∷ s₁) ∣ s₂ ;
                                               output = o }
-- end of while loop                      
oneStepEval (record { st     = s ;
                      stack  = l@(x ∷ xs) ;
                      cmds   = d@(s₁ ∣ (cmd@(n , (whileEnd e)) ∷ s₂)) ;
                      output = o }) with evalExp e s ≡ᵈ nil
... | true  = record { st     = s ;
                       stack  = xs ;
                       cmds   = (cmd ∷ s₁) ∣ s₂ ;
                       output = o }
... | false = record { st     = s ;
                       stack  = l ;
                       cmds   = goBackTo x d ;
                       output = o }
-- end of pg -- do nothing
oneStepEval r = r
