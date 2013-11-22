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
    noU : Float → Units
    meter   : Float → Units
    gram  : Float → Units
    second   : Float → Units
    _u×_   : Units → Units → Units
    _^-1   : Units → Units

  reduce : Units → (Float → Units)
  reduce x = {!!}


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
  un (x u× y) = reduce (un x 1.0 u× un y 1.0)
  un (x ^-1) = {!!}
  

{-
  data operator : Set where
    `+ : operator
    `× : operator
-}
    
  _``+_ : Units → Units → Units
  _``+_ u1 u2 = {!!}
  
  data exp : Units → Set where
    V  : (y : Units) → exp y
    `+ : {x y : Units} → exp x → exp y → (un x) == (un y) → exp ((un x) (primFloatPlus (Val y) (Val x)))
    `- : {x y : Units} → exp x → exp y → (un x) == (un y) → exp ((un x) (primFloatMinus (Val y) (Val x)))
    `× : {x y : Units} → exp x → exp y → exp (x u× y)
    `÷ : {x y : Units} → exp x → exp y → exp (x u× (y ^-1))

  x : exp(meter(2.0))
  x = `+ (V (meter (1.0))) (V(second(1.0))) Refl

{-
  data eq : exp → Units → Set where
    eN : eq ? ?
    _`+_  : ? 
    _`-_  : ?
    _`×_  : ?
    _`÷_  : ?   
-} 
{-
  Data : dim → Float → prefix → Units
  Data scalar = noU
  Data length = meter
  Data mass = gram
  Data time = second
  Data (d `× d1) = {!!}
  Data (d ^-1) = {!!}
-}
--  data NatU where
--    D : Nat → dim → NatD

--  S : {t x : Units} second → meter
-- S t = 