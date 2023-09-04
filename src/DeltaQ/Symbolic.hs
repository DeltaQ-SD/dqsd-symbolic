{-# LANGUAGE DeriveAnyClass, DeriveGeneric #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module DeltaQ.Symbolic where

import GHC.Generics (Generic)

import DeltaQ.Class

data Sym w x = Perfection | Bottom | Delta x | Uniform x
             | Convolve (Sym w x) (Sym w x) | ProbChoice w (Sym w x) (Sym w x)
             | All [Sym w x] | First [Sym w x]
  deriving (Eq, Show, Ord, Num, Fractional, Real, Generic)



{- Normal form
  * promotes ⊥ to up and to the left
  * demotes ∅ down and to the right
  in any expression.
-}

normaliseDeltaQ :: (Ord w, Fractional w, Show w)
                   => Sym w x -> Sym w x

-- eliminate redundant choices when both terms are ⊥ or ∅
normaliseDeltaQ (ProbChoice _ Bottom Bottom)
  = Bottom
normaliseDeltaQ (ProbChoice _ Perfection Perfection)
  = Perfection

-- eliminate redundant branching if probability is 0 or 1.  use of <=
-- and >= is to permit (however unwisely) Real versions of probability
normaliseDeltaQ (ProbChoice prob a b)
  | prob <= 0  = normaliseDeltaQ b -- a has no influence
  | prob >= 1  = normaliseDeltaQ a -- b has no influence

-- normalise the position of ⊥ and ∅
normaliseDeltaQ (ProbChoice p a Bottom)
  = let a' = normaliseDeltaQ a
    in normaliseDeltaQ $ ProbChoice (1-p) Bottom a'
normaliseDeltaQ (ProbChoice p Perfection b)
  = let b' = normaliseDeltaQ b
    in normaliseDeltaQ $ ProbChoice (1-p) b' Perfection

-- structural re-writes for ProbChoice
-- ⊥ concatenation
normaliseDeltaQ (ProbChoice p Bottom (ProbChoice q Bottom x))
  = let x' = normaliseDeltaQ x
    in normaliseDeltaQ $ ProbChoice ( p + (1-p) * q) Bottom x'
--
-- visualisation of ⊥ concatenation:
--       A                                                 A
--   (p)/ \(1-p)     noting that               (p+(1-p)*q)/ \((1-p)*(1-q))
--     ⊥   B                       becomes               ⊥  x
--     (q)/ \(1-q)   the ⊥ branch
--       ⊥   x       B probability             and that 1 - (p+(1-p*q) = (1-p)*(1-q)
--                   is (1-p)*q

-- ∅ demotion
normaliseDeltaQ (ProbChoice q (ProbChoice p x Perfection) y)
    = let x' = normaliseDeltaQ x
          y' = normaliseDeltaQ y
      in normaliseDeltaQ $ ProbChoice (p*q) x' (ProbChoice ((1 - q)/(1 - p*q)) y' Perfection)

-- operational identities for ⊕
normaliseDeltaQ (Convolve Bottom _)
  = Bottom
normaliseDeltaQ (Convolve _ Bottom)
  = Bottom
normaliseDeltaQ (Convolve Perfection y)
  = normaliseDeltaQ y
normaliseDeltaQ (Convolve x Perfection)
  = normaliseDeltaQ x

-- ⊥ promotion
normaliseDeltaQ (Convolve (ProbChoice p Bottom x) y)
  = normaliseDeltaQ $ ProbChoice p Bottom (Convolve x y)
normaliseDeltaQ (Convolve x (ProbChoice p Bottom y))
  = normaliseDeltaQ $ ProbChoice p Bottom (Convolve x y)

-- ∅ elimination
normaliseDeltaQ (Convolve (ProbChoice p x Perfection) y)
  = normaliseDeltaQ $ ProbChoice p (Convolve x y) y
normaliseDeltaQ (Convolve x (ProbChoice p y Perfection))
  = normaliseDeltaQ $ ProbChoice p (Convolve x y) x

-- delay model simplification
--normaliseDeltaQ x@(Convolve (Delay _) (Delay _))
-- = simplifyDelay normaliseDeltaQ x
normaliseDeltaQ x = x



instance (Num x, Ord x, Fractional x, Fractional w, Real w, Show x, Show w) => ImproperRandomVariable (Sym w x) where
  type DelayModel       (Sym w x) = x
  type ProbabilityModel (Sym w x) = Sym w x
  
  perfection = Perfection
  bottom     = Bottom
  diracDelta = Delta
  uniform0   = Uniform
  
  tangibleMass Perfection  = Perfection
  tangibleMass Bottom      = Bottom
  tangibleMass (Delta _)   = Perfection
  tangibleMass (Uniform _) = Perfection
  
  tangibleMass (Convolve a b) = fromRational $ toRational (tangibleMass a) * toRational (tangibleMass b)
  tangibleMass (ProbChoice p a b)
      = fromRational $ toRational p * toRational (tangibleMass a)
        + (1 - toRational p) * toRational (tangibleMass b)
        
  tangibleMass (First xs) = undefined
  tangibleMass (All   xs) = undefined

instance Convolvable (Sym w x) where
  convolve = Convolve

instance Fractional w => NonConcurrentCombination w (Sym w x) where
  probabilisticChoice = ProbChoice

instance ConcurrentCombination (Sym w x) where
  firstToFinish' = First
  allToFinish'   = All

