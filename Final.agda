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
  
  data BaseU : Set where
    noU      : BaseU
    meter    : BaseU
    meter-   : BaseU
    gram     : BaseU
    gram-    : BaseU
    second   : BaseU
    second-  : BaseU
    ampere   : BaseU
    ampere-  : BaseU
    kelvin   : BaseU
    kelvin-  : BaseU
    candela  : BaseU
    candela- : BaseU
    mol      : BaseU
    mol-     : BaseU
    
  data Units : Set where
    U        : BaseU → Units
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
  filternoU (x u× (U noU)) = filternoU x
  filternoU (U noU u× x) = filternoU x
  filternoU (x u× x1) with filternoU x | filternoU x1
  ... | U noU | U noU = U noU
  ... | u | U noU = u
  ... | U noU | u = u
  ... | u1 | u2 = u1 u× u2
  filternoU x = x

  flip : Units → Units
  flip (U noU) = U noU
  flip (U meter) = (U meter-)
  flip (U meter-) = (U meter)
  flip (U gram) = U gram-
  flip (U gram-) = U gram
  flip (U second-) = U second-
  flip (U second-) = U second
  flip (U ampere) = U ampere-
  flip (U ampere-) = U ampere
  flip (U kelvin) = U kelvin-
  flip (U kelvin-) = U kelvin
  flip candela = U candela-
  flip candela- = U candela
  flip mol = U mol-
  flip mol- = U mol
  flip (x1 u× x2) = (flip x1) u× (flip x2)

  cancel : Units → Units → Units
  cancel (U noU) x = x
  cancel (U meter) (U noU) = (U meter)
  cancel (U meter) (U meter-) = U noU
  cancel (U meter) (noU u× y1) = cancel (U meter) y1
  cancel (U meter) ((U meter-) u× y1) = y1
  cancel (U meter) ((y u× y1) u× y2) = cancel (U meter) (y u× (y1 u× y2))
  cancel (U meter) (x u× y) = x u× cancel (U meter) y
  cancel (U meter-) (U noU) = U meter-
  cancel (U meter-) (U meter) = U noU
  cancel (U meter-) (noU u× y1) = cancel (U meter-) y1
  cancel (U meter-) ((U meter) u× y1) = y1
  cancel (U meter-) ((y u× y1) u× y2) = cancel (U meter-) (y u× (y1 u× y2))
  cancel (U meter-) (x u× y) = x u× cancel (U meter-) y
  cancel (U gram) (U noU) = U gram
  cancel (U gram) (U gram-) = U noU
  cancel (U gram) (noU u× y1) = cancel (U gram) y1
  cancel (U gram) ((U gram-) u× y1) = y1
  cancel (U gram) ((y u× y1) u× y2) = cancel (U gram) (y u× (y1 u× y2))
  cancel (U gram) (x u× y) = x u× cancel (U gram) y
  cancel (U gram-) (U noU) = U gram-
  cancel (U gram-) (U gram) = U noU
  cancel (U gram-) (U noU u× y1) = cancel (U gram-) y1
  cancel (U gram-) ((U gram) u× y1) = y1
  cancel (U gram-) ((y u× y1) u× y2) = cancel (U gram-) (y u× (y1 u× y2))
  cancel (U gram-) (x u× y) = x u× cancel (U gram-) y
  cancel (U second-) (U noU) = U second
  cancel (U second-) (U second-) = U noU
  cancel (U second-) (noU u× y1) = cancel (U second-) y1
  cancel (U second-) ((U second-) u× y1) = y1
  cancel (U second-) ((y u× y1) u× y2) = cancel (U second-) (y u× (y1 u× y2))
  cancel (U second-) (x u× y) = x u× cancel (U second-) y
  cancel (U second-) (U noU) = U second-
  cancel (U second-) (U second-) = U noU
  cancel (U second-) (U noU u× y1) = cancel (U second-) y1
  cancel (U second-) ((U second) u× y1) = y1
  cancel (U second-) ((y u× y1) u× y2) = cancel (U second-) (y u× (y1 u× y2))
  cancel (U second-) (x u× y) = x u× cancel (U second-) y
  cancel (U ampere) (U noU) = U ampere
  cancel (U ampere) (U ampere-) = U noU
  cancel (U ampere) (U noU u× y1) = cancel (U ampere) y1
  cancel (U ampere) (U ampere- u× y1) = y1
  cancel (U ampere) ((y u× y1) u× y2) = cancel (U ampere) (y u× (y1 u× y2))
  cancel (U ampere) (x u× y) = x u× cancel (U ampere) y
  cancel (U ampere-) (U noU) = U ampere-
  cancel (U ampere-) (U ampere) = U noU
  cancel (U ampere-) (noU u× y1) = cancel (U ampere-) y1
  cancel (U ampere-) ((U ampere) u× y1) = y1
  cancel (U ampere-) ((y u× y1) u× y2) = cancel (U ampere-) (y u× (y1 u× y2))
  cancel (U ampere-) (x u× y) = x u× cancel (U ampere-) y
  cancel (U kelvin) (U noU) = U kelvin
  cancel (U kelvin) (U kelvin-) = U noU
  cancel (U kelvin) (U noU u× y1) = cancel (U kelvin) y1
  cancel (U kelvin) (U kelvin- u× y1) = y1
  cancel (U kelvin) ((y u× y1) u× y2) = cancel (U kelvin) (y u× (y1 u× y2))
  cancel (U kelvin) (x u× y) = x u× cancel (U kelvin) y
  cancel (U kelvin-) (U noU) = U kelvin-
  cancel (U kelvin-) (U kelvin) = U noU
  cancel (U kelvin-) (U noU u× y1) = cancel (U kelvin-) y1
  cancel (U kelvin-) (U kelvin u× y1) = y1
  cancel (U kelvin-) ((y u× y1) u× y2) = cancel (U kelvin-) (y u× (y1 u× y2))
  cancel (U kelvin-) (x u× y) = x u× cancel (U kelvin-) y
  cancel (U candela (U noU) = U candela
  cancel (U candela U candela- = U noU
  cancel (U candela (noU u× y1) = cancel U candela y1
  cancel (U candela (U candela- u× y1) = y1
  cancel (U candela ((y u× y1) u× y2) = cancel candela (y u× (y1 u× y2))
  cancel (U candela (x u× y) = x u× cancel candela y
  cancel (U candela- (U noU) = candela-
  cancel (U candela- candela = noU
  cancel (U candela- (noU u× y1) = cancel candela- y1
  cancel (U candela- (candela u× y1) = y1
  cancel (U candela- ((y u× y1) u× y2) = cancel candela- (y u× (y1 u× y2))
  cancel (U candela- (x u× y) = x u× cancel candela- y
  cancel (U mol (U noU) = mol
  cancel (U mol mol- = noU
  cancel (U mol (noU u× y1) = cancel mol y1
  cancel (U mol (mol- u× y1) = y1
  cancel (U mol ((y u× y1) u× y2) = cancel mol (y u× (y1 u× y2))
  cancel (U mol (x u× y) = x u× cancel mol y
  cancel (U mol- (U noU) = mol-
  cancel (U mol- mol = noU
  cancel (U mol- (noU u× y1) = cancel mol- y1
  cancel (U mol- (mol u× y1) = y1
  cancel (U mol- ((y u× y1) u× y2) = cancel mol- (y u× (y1 u× y2))
  cancel (U mol- (x u× y) = x u× cancel mol- y
  cancel x y = x u× y

  reduce : Units → Units
  reduce (noU u× u1) = reduce u1
  reduce (u1 u× noU) = reduce u1
  reduce ((u u× u1) u× u2) = reduce (u u× (u1 u× u2))
  reduce (u u× u1) = cancel u (reduce u1)
  reduce u = u

  v : Units
  v = (U meter) u× meter-
  v' : Units
  v' = ((U meter) u× second) u× (((U second-) u× second-))
  testv' : (reduce v') == ((U meter) u× second-)
  testv' = Refl
  testv : reduce v == noU
  testv = Refl

  order : Units → Units
  order (noU u× u2) = order u2
  order ((U meter) u× u2) = (U meter) u× order u2
  order ((U meter-) u× u2) = order u2 u× (U meter-
  order ((U gram) u× u2) = {!!}
  order ((U gram-) u× u2) = {!!}
  order ((U second) u× u2) = {!!}
  order ((U second-) u× u2) = {!!}
  order ((U ampere) u× u2) = {!!}
  order (ampere- u× u2) = {!!}
  order (kelvin u× u2) = {!!}
  order (kelvin- u× u2) = {!!}
  order (candela u× u2) = {!!}
  order (candela- u× u2) = {!!}
  order (mol u× u2) = {!!}
  order (mol- u× u2) = {!!}
  order (u1 u× u2 u× u3) = {!!}
  order u = u
  
  isBase : Units → Bool
  isBase u = ?
  
  
 --floats all units of type units to the front
  order-u : Units → Units → Units
  order-u (u u× us) = (U meter) u× (order-u us)
  order-u (u u× us) = order us u× u
  order-u u = u



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
  g : UF ((U meter) u× ((U second-) u× second-))
  g = V (~ 9.8) ((U meter) u× ((U second-) u× second-))

--  displacement : UF (U second-) → UF (U meter)
--  displacement t = V 0.5 (U noU) `× g `× t `× t

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
    cos : UF (U noU) → UF noU
    cos θ = V (primSin (primFloatMinus (primFloatDiv π 2.0) (compute θ))) noU
    sin : UF (U noU) → UF noU
    sin θ = V (primSin (compute θ)) noU
--    sqrt : {u : Units} → UF u → UF u
--    sqrt = {!!}
    g' : UF ((U meter) u× ((U second-) u× second-))
    g' = V (~ 9.8) ((U meter) u× ((U second-) u× second-))

    h-dist-trav : UF ((U meter) u× second-)                --velocity
                  → UF (U noU)                             --angle
                  → UF ((U meter) u× ((U second-) u× second-)) -- gravitational constant
                  → UF (U meter)                           -- distance traveled
    h-dist-trav v θ g = ((v `× cos θ) `÷ g') `× ((V 2.0 noU) `× (v `× sin θ))

    max-height : UF ((U meter) u× second-)   --velocity
                → UF (U noU)                               --angle
                → UF (U meter)                             -- initial height
                → UF ((U meter) u× ((U second-) u× second-)) -- gravitational constant
                → UF (U meter)                                -- maximum height
    max-height v θ y₀ g = ((v `× v `× sin θ `× sin θ) `÷ ((V (~ 2.0) noU) `× g')) `+ y₀

    treduce :  Units
    treduce = reduce (noU u× ((U meter) u× ((U second-) u× second-)))

    vtest : UF ((U meter) u× second-)
    vtest = V 1.0 (U meter) `÷ V 1.0 second
{-    v2test : UF (((U meter) u× (U meter)) u× ((U second-) u× second-))
    v2test = vtest `× vtest
    gytest : UF ((U meter) u× (U meter) u× ((U second-) u× second-))
    gytest = V 2.0 (U noU) `× V (~ 9.8) ((U meter) u× ((U second-) u× second-)) `× V 1.0 (U meter)
    v2gy : UF ((U meter) u× (U meter) u× ((U second-) u× second-))
    v2gy = v2test `+ gytest

    sqrt-test : (UF ((U meter) u× second-))
    sqrt-test = {!`√ v2gy!}
-}
