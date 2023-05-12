{-# OPTIONS --allow-unsolved-metas #-}
module Arithmetic where


open import BuiltIn
open import List



a≤b&b=c=>a≤c : (a b c : Nat) -> ((a ≤ b) × (b ≡ c)) -> a ≤ c
a≤b&b=c=>a≤c a b .b (a≤b ^ refl) = a≤b

c=0=>a*c=0 : (a c : Nat) -> (c ≡ 0) -> ((a * c) ≡ 0)
c=0=>a*c=0 a c c=0 = {!!}

a≤b&b≤a=>a=b : (a b : Nat) -> ((a ≤ b) × (b ≤ a)) -> (a ≡ b)
a≤b&b≤a=>a=b a b (a≤b ^ b≤a) = {!!}

c!=0&a=b=>a≤bc : (a b c : Nat) -> ((c ≡ 0 -> ⊥) × (a ≡ b)) -> (a ≤ (b * c))
c!=0&a=b=>a≤bc a b c (c!=0 ^ a=b) = {!!}

aInRangeB : (a b : Nat) -> a ≤ b -> (isIn Nat a (range b))
aInRangeB a b a≤b = {!!}

only≤Divides : (a b : Nat) -> ((a ≡ b -> ⊥) × (b ≤ a)) -> (divides a b) -> ⊥
only≤Divides a b (aNeqb ^ b≤a) a|b = let
                                         a|b2 = (snd a|b)
                                         c    = (car a|b2)
                                         ac=b = (cdr a|b2)
                                     in  aNeqb $ a≤b&b≤a=>a=b a b (a≤b&b=c=>a≤c a (a * c) b (c!=0&a=b=>a≤bc a a c ((λ c=0 -> (fst a|b) $ trans (sym $ cdr (snd a|b)) (c=0=>a*c=0 a c c=0)) ^ refl) ^ ac=b) ^ b≤a)

--works by showing that a=a => a≤ac because c!=0 then using that we show that because ac=b that a≤ac => a≤b thus because a≤b and b≤a we get a=b which gives us a contradictiona
--c!=0 is shown by assuming c and showing that b=0 which is false by def of division


≤EitherRefl : (a b : Nat) -> Either (a ≤ b) (b ≤ a)
≤EitherRefl = {!!}
