include "basics/pts.ma".
include "basics/logic.ma".

definition id : ∀A:Type[0]. A → A ≝ λA, x. x.

(* Notation *)
notation "hvbox(x break \times y)" right associative with precedence 70
for @{ 'product $x $y}.

notation "hvbox(a break + b)" right associative with precedence 65
for @{ 'plus $a $b }.

notation "𝟙" with precedence 90 for @{ 'one }.
notation "〈〉" with precedence 90 for @{ 'unit }.

notation "λ〈 ident x , ident y 〉 . term 19 e" with precedence 20 for 
 @{'uncurry (λ ${ident x}, ${ident y}. $e)}.

(* we use ; as the separator to denote nested tuple matching.
Thus the notation λ〈a;b;c〉.e stands for λ〈a,〈b,〈c,〈〉〉〉〉.e if that were legal. *)
notation > "hvbox (λ〈 list0 ident x sep ; 〉 . term 19 e)" with precedence 20
  for ${ fold right @{'point $e} rec acc @{'uncurry (λ${ident x}.$acc)} }.

notation "𝟘" with precedence 90 for @{ 'zero }.

notation "σ1" with precedence 90 for @{ 'sigma1 }.
notation "σ2" with precedence 90 for @{ 'sigma2 }.

notation "[ f , g ]" with precedence 90 for @{ 'either $f $g }.

(* we use ; as the separator to denote nested tuple matching.
Thus the notation [f;g;h] stands for [f,[g,[h,[]]]]. *)
notation > "hvbox ([ list0 f sep ; ])" with precedence 90
  for ${ fold right @{'void} rec acc @{'either $f $acc} }.

notation "𝕀" with precedence 90 for @{ 'id }.

interpretation "identity function" 'id = (id ?).

notation "𝕂" with precedence 90 for @{ 'const }.

notation "〚A〛" with precedence 90 for @{ 'interp $A }.

(* Types *)

inductive oneT : Type[0] ≝ neo : oneT.

interpretation "One Type" 'one = oneT.

interpretation "One Consturctor" 'unit = neo.

definition point : ∀C:Type[1]. C → 𝟙 → C ≝
λC, c, x. match x with [neo ⇒ c].

interpretation "Unit Eliminator" 'point x = (point ? x).

inductive prodT (A, B : Type[0]) : Type[0] ≝
| pair : A → B → prodT A B.

interpretation "Product Type" 'product x y = (prodT x y).

interpretation "Product Constructor" 'pair x y = (pair ? ? x y).

definition map_prodT : ∀A1, B1, A2, B2 : Type[0].
 (A1 → B1) → (A2 → B2) → (A1 × A2) → (B1 × B2) ≝
 λA1, B1, A2, B2, f1, f2, x. match x with [pair x1 x2 ⇒ 〈f1 x1, f2 x2〉].

interpretation "Product Bi-functor" 'product f g = (map_prodT ? ? ? ? f g).

definition uncurry : ∀A, B : Type[0]. ∀C : Type[1]. (A → B → C) → (A × B) → C ≝
 λA, B, C, f, x. match x with [pair x1 x2 ⇒ f x1 x2].

interpretation "Uncurry" 'uncurry f = (uncurry ? ? ? f).

inductive zeroT : Type[0] ≝.

interpretation "Zero Type" 'zero = zeroT.

definition void : ∀C:Type[1]. 𝟘 → C ≝ 
λC, x. match x in zeroT return λ_.C with [].

interpretation "zeroT Eliminator" 'void = (void ?).

inductive sumT (A, B : Type[0]) : Type[0] ≝
| sigma1 : A → sumT A B
| sigma2 : B → sumT A B.

interpretation "Sum Type" 'plus x y = (sumT x y).

interpretation "Sum Constructor 1" 'sigma1 x = (sigma1 ? ? x).
interpretation "Sum Constructor 2" 'sigma2 x = (sigma2 ? ? x).

definition map_sumT : ∀A1, B1, A2, B2 : Type[0].
 (A1 → B1) → (A2 → B2) → (A1 + A2) → (B1 + B2) ≝
 λA1, B1, A2, B2, f1, f2, x. match x with [sigma1 x1 ⇒ σ1 (f1 x1)
                                          |sigma2 x2 ⇒ σ2 (f2 x2)
                                          ].

interpretation "Sum Bi-functor" 'plus f g = (map_sumT ? ? ? ? f g).

definition either : ∀A, B : Type[0]. ∀C : Type[1]. (A → C) → (B → C) → (A + B → C) ≝
 λA, B, C, f, g, x. match x with [sigma1 x1 ⇒ f x1
                                 |sigma2 x2 ⇒ g x2
                                 ].

interpretation "sumT eliminator" 'either f g = (either ? ? ? f g).

(* Contianers *)

(* A container is a function of type c : A → Type[0] for some A (aka c : ΣA:Type[0].A -> Type[0])
   The functor for a container c is λX:Type[0]. Σx:A.c x → X.
   The sum of two cointainers c1 : A1 → Type[0] and c2 : A1 → Type[0] is (either ? ? ? c1 c2) : (A1 + A2) → Type[0].
   The product of two cointainers c1 : A1 → Type[0] and c2 : A1 → Type[0] is (λ〈x1,x2〉. c1 x1 + c2 x2) : (A1 × A2) → Type[0].
   The null containter (additive unit) is (void Type[0]) : ⊥ → Type[0].
   The unit containter (multiplicative unit) is (λ〈〉. ⊥) : ⊤ → Type[0].
   The identity container is (λ〈〉. ⊤) : ⊤ → Type[0].
   (composition of containters ...)
   (plethory operations?)
*)

record Container : Type[1] ≝
{ shape : Type[0]
; pos : shape → Type[0]
}.

definition constC : Type[0] → Container ≝ 
 λA. mk_Container A (λ_. 𝟘).

definition oneC : Container ≝ constC 𝟙.

interpretation "One Container" 'one = oneC.

definition prodC : Container → Container → Container ≝
λA, B. mk_Container ((shape A) × (shape B))
 (λ〈a,b〉. pos A a + pos B b).

interpretation "Product Container" 'product x y = (prodC x y).

definition zeroC : Container ≝ constC 𝟘.

interpretation "Zero Container" 'zero = zeroC.

definition sumC : Container → Container → Container ≝
λA, B. mk_Container (shape A + shape B) [pos A, pos B].

interpretation "Sum Container" 'plus x y = (sumC x y).

interpretation "Constant Container" 'const = constC. 

definition identC : Container ≝ mk_Container 𝟙  (λ_. 𝟙) (* alternative: λ〈〉. 𝟙 *).

interpretation "Identity Container" 'id = identC.

inductive interpretC (A:Container) (X:Type[0]) : Type[0] ≝
 contain : ∀s:shape A. (pos A s → X) → interpretC A X.

interpretation "Container Interpretation" 'interp x = (interpretC x).

definition constC_isoA : ∀A, X:Type[0]. A → 〚𝕂A〛X ≝
 λA, X, a. contain (𝕂A) X a [].

definition constC_isoB : ∀A, X:Type[0]. 〚𝕂A〛X → A ≝
 λA, X, x. match x with [contain s f ⇒ s].

interpretation "Unit Containter Interpretation" 'unit = (constC_isoA ? ? neo).

definition prodC_isoA : ∀A, B:Container. ∀X:Type[0].  ((〚A〛X) × (〚B〛X)) → 〚A × B〛X ≝
 λA, B, X, x. match x with
 [pair x1 x2 ⇒ match x1 with 
              [contain s1 f1 ⇒ match x2 with
              [contain s2 f2 ⇒ contain (A × B) X 〈s1,s2〉 [f1, f2]
 ]            ]].

definition prodC_isoB : ∀A, B:Container. ∀X:Type[0].  〚A × B〛X → ((〚A〛X) × (〚B〛X)) ≝
 λA, B, X, x. match x with
 [contain s f ⇒ match s return λs. (pos (A × B) s → X) → ((〚A〛X) × (〚B〛X)) with
                [pair s1 s2 ⇒ λf0. 〈contain A X s1 (λy. f0 (σ1 y)), contain B X s2 (λy. f0 (σ2 y))〉
                ] f
 ].

interpretation "Product Containter Interpretation" 'pair x y = (prodC_isoA ? ? ? (pair ? ? x y)).

definition sumC_isoA : ∀A, B:Container. ∀X:Type[0].  ((〚A〛X) + (〚B〛X)) → 〚A + B〛X ≝
 λA, B, X, x. match x with
 [sigma1 x1 ⇒ match x1 with 
              [contain s f ⇒ contain (A + B) X (σ1 s) f]
 |sigma2 x2 ⇒ match x2 with
              [contain s f ⇒ contain (A + B) X (σ2 s) f]
 ].

definition sumC_isoB : ∀A, B:Container. ∀X:Type[0].  〚A + B〛X → ((〚A〛X) + (〚B〛X)) ≝
 λA, B, X, x. match x with
 [contain s f ⇒ match s return λs. (pos (A + B) s → X) → ((〚A〛X) + (〚B〛X)) with
                [sigma1 s1 ⇒ λf0. σ1 (contain A X s1 f0)
                |sigma2 s2 ⇒ λf0. σ2 (contain B X s2 f0)
                ] f
 ].

interpretation "Sum Container Intepretation 1" 'sigma1 x = (sumC_isoA ? ? ? (sigma1 ? ? x)).
interpretation "Sum Container Intepretation 2" 'sigma2 x = (sumC_isoA ? ? ? (sigma2 ? ? x)).

definition idC_isoA : ∀X:Type[0]. X → 〚𝕀〛X ≝
 λX, x. contain 𝕀 X 〈〉 (λ_.x).

definition idC_isoB : ∀X:Type[0]. 〚𝕀〛X → X ≝
 λX, x. match x with [contain s f ⇒ f 〈〉].

inductive W (A:Container) : Type[0] ≝ 
 roll : 〚A〛(W A) → W A.

definition unroll : ∀A : Container. W A → 〚A〛(W A) ≝ 
 λA, x. match x with [roll y ⇒ y].

notation "hvbox(𝐖 ident i opt (: ty) break . p)"
  with precedence 20
for @{ W (mk_Container ? 
          ${default
            @{\lambda ${ident i} : $ty. $p}
            @{\lambda ${ident i} . $p}}) }.

(* Mathescheme primitives *)

notation "hvbox(ι ident i : ty break . p)"
 right associative with precedence 20
for @{'iota (\lambda ${ident i} : $ty. $p) }.

notation "hvbox(ι ident i break . p)"
  with precedence 20
for @{'iota (\lambda ${ident i}. $p) }.

notation "hvbox(ɛ ident i : ty break . p)"
 right associative with precedence 20
for @{'epsilon (\lambda ${ident i} : $ty. $p) }.

notation "hvbox(ɛ ident i break . p)"
  with precedence 20
for @{'epsilon (\lambda ${ident i}. $p) }.

notation > "'if' term 19 e 'then' term 19 t 'else' term 19 f" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
notation < "'if' \nbsp term 19 e \nbsp 'then' \nbsp term 19 t \nbsp 'else' \nbsp term 90 f \nbsp" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.

axiom iota : ∀A : Type[0]. (A → Prop) → A.
axiom epsilon : ∀A : Type[0]. (A → Prop) → A.

interpretation "iota" 'iota x = (iota ? x).

interpretation "epsilon" 'epsilon x = (epsilon ? x).

definition if_then_else : ∀A : Type[0]. Prop → A → A → A ≝
  λA,P,c1,c2. iota ? (λx:A. (x = c1 ∧ P) ∨ (x = c2 ∧ ¬P)).

interpretation "if_then_else" 'if_then_else e t f = (if_then_else ? e t f).

notation "hvbox(∃! ident i : ty break . p)"
 right associative with precedence 20
for @{'existsUnique (λ ${ident i} : $ty. $p) }.

notation < "hvbox(∃! ident i break . p)"
  with precedence 20
for @{'existsUnique (λ ${ident i}. $p) }.

inductive exUniq (A:Type[0]) (P:A → Prop) : Prop ≝
    exUniq_intro: ∀ x:A. P x → (∀ y:A. P y → x = y) → exUniq A P.

interpretation "exists unique" 'existsUnique x = (exUniq ? x).
