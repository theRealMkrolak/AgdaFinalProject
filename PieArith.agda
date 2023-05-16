data Bool : Set where
  true  : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
{-# BUILTIN NATURAL Nat #-}


_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = (n * m) + m


data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 4 _≡_

  -- symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

  -- transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

  -- congruence of equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl



begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_


+0= : (b : Nat) → b ≡ (b + 0)
+0= 0       = refl 
+0= (suc b) = cong suc (+0= b)

+1= : (b : Nat) → suc b ≡ (b + 1)
+1= 0       = refl 
+1= (suc b) = sym (
  begin
    suc b + 1
  =⟨⟩
    suc (b + 1)
  =⟨ cong suc (sym (+1= b))⟩
    suc (suc b)
  end )


suc+=+suc : (a b : Nat)  → suc (a + b) ≡ a + suc b
suc+=+suc 0 b       = refl 
suc+=+suc (suc a) b = cong suc (suc+=+suc a b)

comm+ : (a b : Nat) → (a + b) ≡ (b + a)
comm+ 0 b =  -- ????
  begin
    0 + b
  =⟨⟩
    b
  =⟨ +0= b ⟩
    b + 0
  end
comm+ (suc a) b =
  begin
    (suc a) + b
  =⟨⟩
    suc (a + b)
  =⟨ cong suc (comm+ a b) ⟩
    suc (b + a)
  =⟨ suc+=+suc b a ⟩
    b + (suc a)
  end
    
assoc+ : (a b c : Nat) -> (a + (b + c)) ≡ ((a + b) + c)
assoc+ a 0 c =
  begin
    a + (0 + c)
  =⟨⟩
    a + c
  =⟨ cong (λ x → (x + c)) (+0= a)⟩
    (a + 0) + c
  end
assoc+ a (suc b) c =
  begin
    a + (suc b + c)
  =⟨⟩
    a + suc (b + c)
  =⟨ sym ( suc+=+suc a (b + c)) ⟩
    suc (a + (b + c))
  =⟨ cong suc  (assoc+ a b c) ⟩
    suc ((a + b) + c)
  =⟨⟩
    suc (a + b) + c
  =⟨ cong (λ x → (x + c)) (suc+=+suc a b) ⟩
    (a + suc b) + c
  end
    
assoc-flip : (a b c : Nat) -> (a + (b + c)) ≡ (b + (a + c))
assoc-flip a b c =
  (trans (assoc+ a b c)
    (trans (cong (λ x → (x + c)) (comm+ a b))
      (sym (assoc+ b a c))))



*0=0 : (a : Nat) → 0 ≡ (a * 0)
*0=0 0 = refl
*0=0 (suc a) = sym
  (begin
    (suc a) * 0
  =⟨⟩ 
    (a * 0) + 0
  =⟨ sym (+0= (a * 0)) ⟩
    a * 0
  =⟨ sym (*0=0 a) ⟩
    0
  end)


*1=1 : (a : Nat) → a ≡ (a * 1)
*1=1 0 = refl
*1=1 (suc a) = sym
  (begin
    (suc a) * 1
  =⟨⟩
    (a * 1) + 1
  =⟨ sym (+1= (a * 1)) ⟩
   suc (a * 1) 
  =⟨ cong suc (sym (*1=1 a)) ⟩
    suc a
  end)

suc-help : (a b : Nat) → b + (a * b) ≡ (suc a) * b
suc-help a b = sym
  (begin
    (suc a) * b
  =⟨⟩
    (a * b) + b
  =⟨ comm+ (a * b) b ⟩ 
    b + (a * b)
  end)

suc-rev : (a b : Nat) → suc ( a + b) ≡ (suc a) + b
suc-rev a b = sym (
  begin
    (suc a) + b
  =⟨⟩
    suc ( a + b)
  end )
 

*suc=+* : ( a b : Nat) → a + (a * b) ≡ a * (suc b)
*suc=+* 0  b      = refl
*suc=+* (suc a) b = sym (
  begin
    suc a * suc b
  =⟨⟩
    (a * suc b) + (suc b)
  =⟨ comm+ (a * suc b) (suc b) ⟩
    suc b + (a * suc b)
  =⟨⟩
    suc (b + (a * suc b))
  =⟨ cong (λ x → suc (b + x)) (sym (*suc=+* a b)) ⟩
    suc (b + (a + (a * b)))
  =⟨ cong suc (assoc-flip b a (a * b)) ⟩
    suc (a + (b + (a * b)))
  =⟨ suc-rev a (b + (a * b)) ⟩
    suc a + (b + (a * b))
  =⟨ cong (λ x → (suc a + x)) (suc-help a b) ⟩
    suc a + (suc a * b)
  end ) 


comm* : ( a b : Nat) → a * b ≡ b * a
comm* 0 b = 
  begin
    0 * b
  =⟨⟩
    0
  =⟨ *0=0 b ⟩
    b * 0
  end
comm* (suc a) b =
  begin
    (suc a) * b
  =⟨⟩
    (a * b) + b
  =⟨ cong (λ (x) → (x + b)) (comm* a b) ⟩
    (b * a) + b
  =⟨ comm+ (b * a) b ⟩
    b + (b * a)
  =⟨ *suc=+* b a ⟩
    b * (suc a)
  end


distr+* : (a b c : Nat) → (a + b) * c ≡ (a * c) + (b * c)
distr+* 0 b c = refl
distr+* (suc a) b c = -- {! !}
  begin
    (suc a + b) * c
  =⟨⟩
    suc ( a + b) * c
  =⟨⟩
    (( a + b) * c) + c
  =⟨ cong (λ x → (x + c)) (distr+* a b c) ⟩
    ((a * c) + (b * c)) + c
  =⟨ comm+ ((a * c) + (b * c)) c ⟩
    c + ((a * c) + (b * c))
  =⟨ assoc+ c (a * c) (b * c)  ⟩
    (c + (a * c)) + (b * c)
  =⟨ cong (λ x → (x + (b * c))) (suc-help a c) ⟩
    ( suc a * c ) + (b * c)
  end
    
distr*+ : (a b c : Nat) → a * (b + c) ≡ (a * b) + (a * c)
distr*+ a b c =
  trans
    (comm* a (b + c))
    (trans
      (distr+* b c a)
      (trans
        (cong (λ x → (x + (c * a))) (comm* b a) )
        (cong (λ x → ((a * b) + x)) (comm* c a))))


assoc* : (a b c : Nat) → a * (b * c) ≡ (a * b) * c
assoc* 0 b c = refl
assoc* (suc a) b c = --  {! !}
  begin
    suc a * (b * c)
  =⟨⟩
    (a * (b * c)) + (b * c)
  =⟨ cong (λ x → x + (b * c)) (assoc* a b c) ⟩
    ((a * b) * c) + (b * c)
  =⟨ sym ( distr+*  (a * b) b c ) ⟩
    ((a * b) + b) * c
  =⟨ cong (λ x → x * c) (comm+ (a * b) b) ⟩
    (b + (a * b)) * c
  =⟨ cong (λ x → x * c) (suc-help a b) ⟩
    (suc a * b) * c
  end
    
    
    
    
    
    
    
