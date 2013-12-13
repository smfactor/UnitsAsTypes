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
    primSin          : Float → Float
    primFloatLess    : Float → Float → Bool

--  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)
  
  _f+_ : Float → Float → Float
  x f+ y = primFloatPlus x y
 
  _f−_ : Float → Float → Float --\minus
  x f− y = primFloatMinus x y

  _f×_ : Float → Float → Float --\times
  x f× y = primFloatTimes x y

  _f÷_ : Float → Float → Float --\div
  x f÷ y = primFloatDiv x y
 
  ~_ : Float → Float
  ~ x = primFloatMinus 0.0 x

  infix 10 ~_

  abs : Float → Float
  abs x with primFloatLess x 0.0 
  abs x | True = ~ x
  abs x | False = x
  
  π : Float
  π = 3.1415926

  cosine : Float → Float
  cosine θ = primSin ((π f÷ 2.0) f− θ)
 

  funct : Float → Float
  funct x = cosine x f− x

  derivative : Float → Float → Float
  derivative x h = ((funct (x f+ h) f− funct (x f− h)) f÷ (2.0 f× h))

  --approximation algorithm for square roots of floats
  -- x : the number to take the square root of t ≥ 0
  -- ε : the relative error tolerance
  -- t : initial guess of root
  newtonian : Float → Float → Float → Float
  newtonian x ε t with primFloatLess (ε f× t) (abs (t f− (x f÷ t)))
  newtonian x ε t | True = newtonian x ε (((x f÷ t) f+ t) f÷ 2.0)
  newtonian x ε t | False = t

  √ : Float → Float
  √ x = newtonian x 0.0000001 2.0
  

    
  data Units : Set where
    noU      : Units
    meter    : Units
    meter-   : Units
    gram     : Units
    gram-    : Units
    second   : Units
    second-  : Units
    ampere   : Units
    ampere-  : Units
    kelvin   : Units
    kelvin-  : Units
    candela  : Units
    candela- : Units
    mol      : Units
    mol-     : Units
    _u×_     : Units → Units → Units

  infixl 10 _u×_


  data Prefix : Set where
    yotta : Prefix
    zetta : Prefix
    exa   : Prefix
    peta  : Prefix
    tera  : Prefix
    giga  : Prefix
    mega  : Prefix
    kilo  : Prefix
    hecto : Prefix
    deca  : Prefix
    deci  : Prefix 
    centi : Prefix
    milli : Prefix
    micro : Prefix
    nano  : Prefix
    pico  : Prefix
    femto : Prefix
    atto  : Prefix
    zepto : Prefix
    yocto : Prefix

  prefixed : Float → Prefix → Float
  prefixed f yotta = f f× 1.0e24
  prefixed f zetta = f f× 1.0e21
  prefixed f exa = f f× 1.0e18
  prefixed f peta = f f× 1.0e15
  prefixed f tera = f f× 1.0e12
  prefixed f giga = f f× 1.0e9
  prefixed f mega = f f× 1000000.0
  prefixed f kilo = f f× 1000.0
  prefixed f hecto = f f× 100.0
  prefixed f deca = f f× 10.0
  prefixed f deci = f f÷ 10.0
  prefixed f centi = f f÷ 100.0
  prefixed f milli = f f÷ 1000.0
  prefixed f micro = f f÷ 1000000.0
  prefixed f nano = f f÷ 1.0e9
  prefixed f pico = f f÷ 1.0e12
  prefixed f femto = f f÷ 1.0e15
  prefixed f atto = f f÷ 1.0e18
  prefixed f zepto = f f÷ 1.0e21
  prefixed f yocto = f f÷ 1.0e24

  

{- Suffix xs ys means that xs is a suffix of ys -}

  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x :: xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y :: ys)

  {- TASK 2.1 : Show that suffix is transitive. -}
  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans Stop Stop = Drop Stop
  suffix-trans Stop (Drop q) =  Drop (suffix-trans Stop q)
  suffix-trans (Drop p) Stop = Drop (suffix-trans p Stop)
  suffix-trans (Drop p) (Drop q) = Drop (suffix-trans p (suffix-trans Stop q))

  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

  filternoU : Units → Units
  filternoU (x u× noU) = filternoU x
  filternoU (noU u× x) = filternoU x
  filternoU (x u× x1) with filternoU x | filternoU x1
  ... | noU | noU = noU
  ... | u | noU = u
  ... | noU | u = u
  ... | u1 | u2 = u1 u× u2
  filternoU x = x

  flip : Units → Units
  flip noU = noU
  flip meter = meter-
  flip meter- = meter
  flip gram = gram-
  flip gram- = gram
  flip second = second-
  flip second- = second
  flip ampere = ampere-
  flip ampere- = ampere
  flip kelvin = kelvin-
  flip kelvin- = kelvin
  flip candela = candela-
  flip candela- = candela
  flip mol = mol-
  flip mol- = mol
  flip (x1 u× x2) = (flip x1) u× (flip x2)

  cancel : Units → Units → Units
  cancel noU x = x
  cancel meter noU = meter
  cancel meter meter- = noU
  cancel meter (noU u× y1) = cancel meter y1
  cancel meter (meter- u× y1) = y1
  cancel meter ((y u× y1) u× y2) = cancel meter (y u× (y1 u× y2))
  cancel meter (x u× y) = x u× cancel meter y
  cancel meter- noU = meter-
  cancel meter- meter = noU
  cancel meter- (noU u× y1) = cancel meter- y1
  cancel meter- (meter u× y1) = y1
  cancel meter- ((y u× y1) u× y2) = cancel meter- (y u× (y1 u× y2))
  cancel meter- (x u× y) = x u× cancel meter- y
  cancel gram noU = gram
  cancel gram gram- = noU
  cancel gram (noU u× y1) = cancel gram y1
  cancel gram (gram- u× y1) = y1
  cancel gram ((y u× y1) u× y2) = cancel gram (y u× (y1 u× y2))
  cancel gram (x u× y) = x u× cancel gram y
  cancel gram- noU = gram-
  cancel gram- gram = noU
  cancel gram- (noU u× y1) = cancel gram- y1
  cancel gram- (gram u× y1) = y1
  cancel gram- ((y u× y1) u× y2) = cancel gram- (y u× (y1 u× y2))
  cancel gram- (x u× y) = x u× cancel gram- y
  cancel second noU = second
  cancel second second- = noU
  cancel second (noU u× y1) = cancel second y1
  cancel second (second- u× y1) = y1
  cancel second ((y u× y1) u× y2) = cancel second (y u× (y1 u× y2))
  cancel second (x u× y) = x u× cancel second y
  cancel second- noU = second-
  cancel second- second = noU
  cancel second- (noU u× y1) = cancel second- y1
  cancel second- (second u× y1) = y1
  cancel second- ((y u× y1) u× y2) = cancel second- (y u× (y1 u× y2))
  cancel second- (x u× y) = x u× cancel second- y
  cancel ampere noU = ampere
  cancel ampere ampere- = noU
  cancel ampere (noU u× y1) = cancel ampere y1
  cancel ampere (ampere- u× y1) = y1
  cancel ampere ((y u× y1) u× y2) = cancel ampere (y u× (y1 u× y2))
  cancel ampere (x u× y) = x u× cancel ampere y
  cancel ampere- noU = ampere-
  cancel ampere- ampere = noU
  cancel ampere- (noU u× y1) = cancel ampere- y1
  cancel ampere- (ampere u× y1) = y1
  cancel ampere- ((y u× y1) u× y2) = cancel ampere- (y u× (y1 u× y2))
  cancel ampere- (x u× y) = x u× cancel ampere- y
  cancel kelvin noU = kelvin
  cancel kelvin kelvin- = noU
  cancel kelvin (noU u× y1) = cancel kelvin y1
  cancel kelvin (kelvin- u× y1) = y1
  cancel kelvin ((y u× y1) u× y2) = cancel kelvin (y u× (y1 u× y2))
  cancel kelvin (x u× y) = x u× cancel kelvin y
  cancel kelvin- noU = kelvin-
  cancel kelvin- kelvin = noU
  cancel kelvin- (noU u× y1) = cancel kelvin- y1
  cancel kelvin- (kelvin u× y1) = y1
  cancel kelvin- ((y u× y1) u× y2) = cancel kelvin- (y u× (y1 u× y2))
  cancel kelvin- (x u× y) = x u× cancel kelvin- y
  cancel candela noU = candela
  cancel candela candela- = noU
  cancel candela (noU u× y1) = cancel candela y1
  cancel candela (candela- u× y1) = y1
  cancel candela ((y u× y1) u× y2) = cancel candela (y u× (y1 u× y2))
  cancel candela (x u× y) = x u× cancel candela y
  cancel candela- noU = candela-
  cancel candela- candela = noU
  cancel candela- (noU u× y1) = cancel candela- y1
  cancel candela- (candela u× y1) = y1
  cancel candela- ((y u× y1) u× y2) = cancel candela- (y u× (y1 u× y2))
  cancel candela- (x u× y) = x u× cancel candela- y
  cancel mol noU = mol
  cancel mol mol- = noU
  cancel mol (noU u× y1) = cancel mol y1
  cancel mol (mol- u× y1) = y1
  cancel mol ((y u× y1) u× y2) = cancel mol (y u× (y1 u× y2))
  cancel mol (x u× y) = x u× cancel mol y
  cancel mol- noU = mol-
  cancel mol- mol = noU
  cancel mol- (noU u× y1) = cancel mol- y1
  cancel mol- (mol u× y1) = y1
  cancel mol- ((y u× y1) u× y2) = cancel mol- (y u× (y1 u× y2))
  cancel mol- (x u× y) = x u× cancel mol- y
  cancel x y = x u× y

  reduce : Units → Units
  reduce (noU u× u1) = reduce u1
  reduce ((u u× u1) u× u2) = reduce (u u× (u1 u× u2))
  reduce (u u× u1) = cancel u (reduce u1)
  reduce u = u

  v : Units
  v = meter u× meter-
  v' : Units
  v' = (meter u× second) u× ((second- u× second-))
  testv' : (reduce v') == (meter u× second-)
  testv' = Refl
  testv : reduce v == noU
  testv = Refl

  data UF : Units → Set where
    V    : (f : Float) → (U : Units) → UF U
    P    : (f : Float) → (p : Prefix) → (U : Units) → UF U
    _`+_ : {U : Units} → UF U → UF U → UF U
    _`-_ : {U : Units} → UF U → UF U → UF U
    _`×_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (filternoU (reduce (U1 u× U2)))
    _`÷_ : {U1 U2 : Units} → UF U1 → UF U2 → UF (filternoU (reduce (U1 u× flip U2)))
--    `√_  : {U : Units} → UF (U u× U) → UF U

  infixl 8 _`×_
--  infixl 8 _`÷_
  infixl 4 _`+_
  infixl 4 _`-_
--  test : UF (
  g : UF (meter u× (second- u× second-))
  g = V (~ 9.8) (meter u× (second- u× second-))

--  displacement : UF second → UF meter
--  displacement t = V 0.5 noU `× g `× t `× t

  compute : {u : Units} → UF u → Float
  compute {u} (V f .u) = f
  compute {u} (P f p .u) = prefixed f p
  compute (x `+ x₁) = compute x f+ compute x₁
  compute (x `- x₁) = compute x f− compute x₁
  compute (x `× x₁) = compute x f× compute x₁
  compute (x `÷ x₁) = compute x f÷ compute x₁
--  compute (`√ x) = √ (compute x)

{-
  data Same : Units → Units → Set where
    Refl  : (u : Units) → (u : Units) → Same u u
    Sym   : (u1 : Units) → (u2 : Units) → reduce u1 == reduce u2 → Same (reduce u1) (reduce u2)
    Trans : {u1 u2 u3 : Units} → reduce u1 == reduce u2 → reduce u2 == reduce u3 → Same (reduce u1) (reduce u3)
-}

--  Equivalent : Set where
--  data Equivalent : Units → Units → Set where
  --  Equiv : (u1 : Units) → (u2 : Units) → count u1 == count u2 → Equivalent u1 u2

  --proof that reduce x is in reduced form
  reduced-X : {!!}
  reduced-X = {!!}


-- Library for example of code
  module Projectile where
    cos : UF noU → UF noU
    cos θ = V (primSin (primFloatMinus (primFloatDiv π 2.0) (compute θ))) noU
    sin : UF noU → UF noU
    sin θ = V (primSin (compute θ)) noU
--    sqrt : {u : Units} → UF u → UF u
--    sqrt = {!!}
    g' : UF (meter u× (second- u× second-))
    g' = V (~ 9.8) (meter u× (second- u× second-))
    t1 : UF (meter u× second-) → UF noU → UF (meter u× second-)
    t1 v θ = v `× cos θ
    t1' : UF (meter u× second-) → UF noU → UF (meter u× second- u× second-) → UF second
    t1' v θ g = v `× cos θ `÷ g
    t1'' : UF (meter u× second-) → UF noU → UF (meter u× second- u× second-) → UF (meter u× second-)
    t1'' v θ g = V 2.0 noU `× (v `× sin θ)
    t1''' : UF (meter u× second-) → UF noU → UF (meter u× second- u× second-) → UF meter
    t1''' v θ g = {!(t1' v θ g) `× (t1'' v θ g)!}
    sec : UF second -> UF second- -> UF noU
    sec s s- = s `× s-
    h-dist-trav : UF (meter u× second-)   --velocity
                  → UF noU                               --angle
                  → UF (meter u× (second- u× second-)) -- gravitational constant
                  → UF meter                                -- distance traveled
    h-dist-trav v θ g = {! ((v `× cos θ) `÷ g') `× ((V 2.0 noU) `× (v `× sin θ)) !}

    max-height : UF (meter u× second-)   --velocity
                → UF noU                               --angle
                → UF meter                             -- initial height
                → UF (meter u× (second- u× second-)) -- gravitational constant
                → UF meter                                -- maximum height
    max-height v θ y₀ g = ((v `× v `× sin θ `× sin θ) `÷ ((V (~ 2.0) noU) `× g'))

    treduce :  Units
    treduce = reduce (noU u× (meter u× (second- u× second-)))
{-
    vtest : UF (meter u× second-)
    vtest = V 1.0 meter `÷ V 1.0 second
    v2test : UF (meter u× meter u× (second- u× second-))
    v2test = vtest `× vtest
    gytest : UF (meter u× meter u× (second- u× second-))
    gytest = V 2.0 noU `× V (~ 9.8) (meter u× (second- u× second-)) `×
               V 1.0 meter
    v2gy : UF (meter u× meter u× (second- u× second-))
    v2gy = v2test `+ gytest

    sqrt-test : (UF (meter u× second-))
    sqrt-test = {!`√ v2gy!}
-}
