open import lib.Preliminaries

module Final where
  
  postulate
    Int    : Set
    Float  : Set

  {-# BUILTIN INTEGER Int #-}
  {-# BUILTIN FLOAT Float #-}

  primitive
    primFloatPlus    : Float → Float → Float
    primFloatMinus   : Float → Float → Float
    primFloatTimes   : Float → Float → Float
    primFloatDiv     : Float → Float → Float

--  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)

{-  data dim : Set where
    scalar : dim
    length : dim
    mass   : dim
    time   : dim
    _`×_   : dim → dim → dim
    _^-1   : dim → dim
-}
{-
  data prefix : Set where
    G : prefix
    M : prefix
    k : prefix
    c : prefix
    m : prefix
    μ : prefix
    O : prefix
-}  

  data Units : Set where
    noU : Units
    meter   : Units
    gram  : Units
    second   : Units
    _u×_   : Units → Units → Units
    _^-1   : Units → Units

  data ExpU : Units → Set where
    lift : (u : Units) → ExpU u
    _`+_ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    _`-_ : (u1 : Units) → (u2 : Units) → ExpU u2 → u1 == u2 → ExpU u2
    _`×_ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (u1 u× u2)
    _`÷_ : (u1 : Units) → (u2 : Units) → ExpU u2 → ExpU (u1 u× u2 ^-1)

  data UF : Set where
    _of_ : Float → Units → UF
  
  val : UF → Float
  val (f of u) = f 

  uns : UF → Units
  uns (f of u) = u

  data Exp : UF → Set where
    V    : (u : UF) → Exp u
    _`+_ : (x : UF) → (y : UF) → Exp y → (uns x == uns y) → Exp ((primFloatPlus (val x) (val y)) of (uns y))
    _`-_ : (x : UF) → (y : UF) → Exp y → (uns x == uns y) → Exp ((primFloatMinus (val x) (val y)) of (uns y))
    _`×_ : (x : UF) → (y : UF) → Exp y → Exp ((primFloatTimes (val x) (val y)) of ((uns x) u× (uns y)))
    _`÷_ : (x : UF) → (y : UF) → Exp y → Exp ((primFloatDiv (val x) (val y)) of ((uns x) u× (uns y) ^-1))


  test : UF
  test = 1.0 of noU
   
  --  _`×_ : {u₁ u₂ : ExpU} → (ExpU u₁) → (ExpU u₂) → ExpU (u₁ u× u₂)
  --  _`÷_ : {u₁ u₂ : ExpU} → (ExpU u₁) → (ExpU u₂) → ExpU (u₁ u× (u₂ ^-1))

 -- u-test : ExpU ((meter u× second ^-1) u× gram)
--  u-test = {!((lift meter) `÷ (lift second)) u× gram!}

{-
  Val : Units → Float
  Val (noU x) = x
  Val (meter x) = x
  Val (gram x) = x
  Val (second x) = x
  Val (x u× y) = primFloatTimes (Val x) (Val y)
  Val (x ^-1) = primFloatDiv 1.0 (Val x)

  un : Units → Float → Units
  un (noU x) = noU
  un (meter x) = meter
  un (gram x) = gram
  un (second x) = second 
  un (x u× y) = {!!} --cancel (un x 1.0 u× un y 1.0)
  un (x ^-1) = λ y → un x y ^-1
  -}

{-
  data operator : Set where
    `+ : operator
    `× : operator
-}
    
 -- _``+_ : Units → Units → Units
 -- _``+_ u1 u2 = {!!}
{-  
  data exp : Units → Set where
    V  : (y : Units) → exp y
    `+ : {x y : Units} → exp x → exp y → (un x) == (un y) → exp ((un x) (primFloatPlus (Val y) (Val x)))
    `- : {x y : Units} → exp x → exp y → (un x) == (un y) → exp ((un x) (primFloatMinus (Val y) (Val x)))
    `× : {x y : Units} → exp x → exp y → exp (x u× y)
    `÷ : {x y : Units} → exp x → exp y → exp (x u× (y ^-1))
-}
--  x : exp(meter(2.0))
--  x = `+ (V (meter (1.0))) (V(second(1.0))) Refl

--  x' : exp(meter(2.0))
--  x' = `+ (V (meter (1.0))) (V(meter(1.0))) Refl
