Gradual Guarantee for Lua, Pallene, and LIR

Tags	g, h ::=  int | fun[★→★]


Lua
~~~

Terms   e  ::=  n | e₁ + e₂ | x | λx.e | e₁(e₂)
Types	τ, σ ::=  int | fun[★→★] | ★
Environments  Γ ::= ∅ | Γ, x : ★


    ---------
    Γ ⊢ n : ★

    Γ ⊢ e₁ : ★    Γ ⊢ e₂ : ★
    ------------------------
    Γ ⊢ e₁ + e₂ : ★

    Γ ∋ x : ★
    ---------
    Γ ⊢ x : ★

    Γ, x : ★ ⊢ e : ★
    ----------------
    Γ ⊢ (λx.e) : ★

    Γ ⊢ e₁ : ★    Γ ⊢ e₂ : ★
    ------------------------
    Γ ⊢ e₁(e₂) : ★

Reductions

    v ::= n | λx.e 
    E ::= □ | E+e | v+E | E(e) | v(E)

    E[n+m] -→ E[o]  where  o = n+m
    E[(λx.e)v] -→ E[e[x:=v]]


Pallene
~~~~~~~

Terms   e  ::=  n | e₁ + e₂ | x | λx:τ.e | e₁(e₂)
Types   σ, τ ::= int | fun[σ→τ] | ★
Environments  Γ ::= ∅ | Γ, x : τ

    -----------
    Γ ⊢ n : int

    Γ ⊢ e₁ : int   Γ ⊢ e₂ : int
    ---------------------------
    Γ ⊢ e₁ + e₂ : int

    Γ ∋ x : τ
    ---------
    Γ ⊢ x : τ

    Γ, x : σ ⊢ e : τ
    ---------------------
    Γ ⊢ (λx.e) : fun[σ→τ]

    Γ ⊢ e₁ : fun[σ→τ]    Γ ⊢ e₂ : σ
    --------------------------------
    Γ ⊢ e₁(e₂) : τ

Reductions

    v ::= n | λx.e 
    E ::= □ | E+e | v+E | E(e) | v(E)

    E[n+m] -→ E[o]  where  o = n+m
    E[(λx.e)v] -→ E[e[x:=v]]

LIR
~~~

Terms   e  ::=  n | e₁ + e₂ | x | λx:τ.e | e₁(e₂) | box[g](e) | unbox[g](e)
Types   σ, τ ::= int | fun[σ→τ] | ★
Environments  Γ ::= ∅ | Γ, x : τ

    -----------
    Γ ⊢ n : int

    Γ ⊢ e₁ : int   Γ ⊢ e₂ : int
    ---------------------------
    Γ ⊢ e₁ + e₂ : int

    Γ ∋ x : τ
    ---------
    Γ ⊢ x : τ

    Γ, x : σ ⊢ e : τ
    ---------------------
    Γ ⊢ (λx.e) : fun[σ→τ]

    Γ ⊢ e₁ : fun[σ→τ]    Γ ⊢ e₂ : σ
    --------------------------------
    Γ ⊢ e₁(e₂) : τ

    Γ ⊢ e : g
    -----------------
    Γ ⊢ box[g](e) : ★

    Γ ⊢ e : ★
    -------------------
    Γ ⊢ unbox[g](e) : g

Reductions

    v ::= n | λx.e | box[g](v)
    E ::= □ | E+e | v+E | E(e) | v(E) | box[g](E) | unbox[g](E)

    E[n+m] -→ E[o]  where  o = n+m
    E[(λx.e)v] -→ E[e[x:=v]]
    E[unbox[g](box[g](v))] -→ E[v]
    E[unbox[g](box[h](v))] -→ panic   if g ≠ h

Compiling Lua to LIR

    ⟪ n ⟫        =  box[int](n)
    ⟪ e₁ + e₂ ⟫  =  box[int](unbox[int](⟪ e₁ ⟫) + unbox[int](⟪ e₂ ⟫))
    ⟪ x ⟫        =  x
    ⟪ λx.e ⟫     =  box[fun[★→★]](λx:★.⟪ e ⟫)
    ⟪ e₁(e₂) ⟫   =  unbox[fun[★→★]](⟪ e₁ ⟫)(⟪ e₂ ⟫)

Compiling Pallene to LIR

    (identity)


Gradual Guarantee
~~~~~~~~~~~~~~~~~

1. Static gradual guarantee.

    If Γ ⊢ e : ★ in Lua then Γ ⊢ ⟪ e ⟫ : ★ in LIR.

2. Dynamic gradual guarantee.

Precision on types of LIR

    τ ⊑ ★

    int ⊑ int

    σ₁ ⊑ σ₂    τ₁ ⊑ τ₂
    -----------------------
    fun[σ₁→τ₁] ⊑ fun[σ₂→τ₂]

Lemma. ⊑ is reflexive and transitive.

Precision on terms of LIR.

Environments   Γ⊑  ::=  ∅  |  Γ⊑, x : σ ⊑ τ

    | ∅ |ₗ              =  ∅
    | Γ⊑, x : σ ⊑ τ |ₗ  =  | Γ⊑ |ₗ, x : σ

    | ∅ |ᵣ              =  ∅
    | Γ⊑, x : σ ⊑ τ |ᵣ  =  | Γ⊑ |ᵣ, x : τ

    | ∅ ∣ₗᵣ             =  ∅
    | Γ, x : τ |ₗᵣ      =  | Γ |ₗᵣ, x : τ ⊑ τ 


The general relation is of the form Γ⊑ ⊢ d ⊑ e : σ ⊑ τ.

Lemma.  If Γ⊑ ⊢ d ⊑ e : σ ⊑ τ then σ ⊑ τ and | Γ⊑ |ₗ ⊢ d : σ and | Γ⊑ |ᵣ ⊢ e : τ.

    ----------------------
    Γ⊑ ⊢ n ⊑ n : int ⊑ int

    Γ⊑ ⊢ d₁ ⊑ e₁ : int ⊑ int   Γ⊑ ⊢ d₂ ⊑ e₂ : int ⊑ int
    ----------------------------------------------------
    Γ⊑ ⊢ d₁ + d₂ ⊑ e₁ + e₂ : int ⊑ int

    Γ⊑ ∋ (x : σ ⊑ τ)
    ------------------
    Γ⊑ ⊢ x ⊑ x : σ ⊑ τ

    Γ⊑, x : σ ⊑ τ ⊢ d ⊑ e : σ′ ⊑ τ′
    ------------------------------------------------
    Γ⊑ ⊢ (λx:σ.d) ⊑ (λx:τ.e) : fun[σ→σ′] ⊑ fun[τ→τ′]

    Γ⊑ ⊢ d₁ ⊑ e₁ : fun[σ→σ′] ⊑ fun[τ→τ′]    Γ⊑ ⊢ d₂ ⊑ e₂ : σ ⊑ τ
    -------------------------------------------------------------
    Γ⊑ ⊢ d₁(d₂) ⊑ e₁(e₂) : σ′ ⊑ τ′

    Γ⊑ ⊢ d ⊑ e : t ⊑ g
    --------------------------
    Γ⊑ ⊢ d ⊑ box[g](e) : t ⊑ ★

    Γ⊑ ⊢ d ⊑ e : g ⊑ ★
    --------------------------
    Γ⊑ ⊢ box[g](d) ⊑ e : ★ ⊑ ★

    Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
    ----------------------------
    Γ⊑ ⊢ unbox[g](d) ⊑ e : g ⊑ ★

    Γ⊑ ⊢ d ⊑ e : t ⊑ ★    t ⊑ g
    ----------------------------
    Γ⊑ ⊢ d ⊑ unbox[g](e) : t ⊑ g


Lemmas:

   Γ⊑ ⊢ d ⊑ e : g ⊑ g
   ----------------------------------
   Γ⊑ ⊢ box[g](d) ⊑ box[g](e) : ★ ⊑ ★

   Γ⊑ ⊢ d ⊑ e : ★ ⊑ ★
   --------------------------------------
   Γ⊑ ⊢ unbox[g](d) ⊑ unbox[g](e) : g ⊑ g




Erasure from LIR to LIR

    ∥ n ∥            =  box[int](n)
    ∥ e₁ + e₂ ∥      =  box[int](unbox[int](∥ e₁ ∥) + unbox[int](∥ e₂ ∥))
    ∥ x ∥            =  x
    ∥ λx:τ.e ∥       =  box[fun[★→★]](λx:★.∥ e ∥)
    ∥ e₁(e₂) ∥       =  unbox[fun[★→★]](∥ e₁ ∥)(∥ e₂ ∥)
    ∥ box[g](e) ∥    =  ∥ e ∥
    ∥ unbox[g](e) ∥  =  ∥ e ∥


Lemma.  If Γ ⊢ e : τ in LIR then Γ ⊢ ∥ e ∥ : ★ in LIR.
        If Γ ⊢ e : τ in LIR then | Γ |ₗᵣ ⊢ e ⊑ ∥ e ∥ : τ ⊑ ★ in LIR.

Lemma.  If Γ ⊢ d ⊑ e : σ ⊑ τ and d -→ d′ then e -↠ e′ and Γ ⊢ d′ ⊑ e′ : σ ⊑ τ

Lemma. Substitution.  If Γ⊑ ⊢ d₁ ⊑ e₁ : σ₁ ⊑ τ₁ and Γ⊑, x : σ₁ ⊑ τ₁ ⊢ d₂ ⊑ e₂ : σ₂ ⊑ τ₂
                      then Γ⊑ ⊢ d₂[x:=d₁] ⊑ e₂[x:=e₁] : σ₂ ⊑ τ₂.

  (+)  easy
  (β)  easy, with substitution


    (unbox[g](box[g](v)) -→ v  on the left

      ⊢ v ⊑ w : g ⊑ ★
      -----------------------
      ⊢ box[g](v) ⊑ w : ★ ⊑ ★
      ---------------------------------
      ⊢ unbox[g](box[g](v)) ⊑ w : g ⊑ ★
   
    -→

      ⊢ v ⊑ w : g ⊑ ★


    (unbox[g](box[g](w)) -→ w  on the right

      ⊢ v ⊑ w : g ⊑ g
      -----------------------
      ⊢ v ⊑ box[g](w) : g ⊑ ★
      ---------------------------------
      ⊢ v ⊑ unbox[g](box[g](w)) : g ⊑ g

    -→

      ⊢ v ⊑ w : g ⊑ g
