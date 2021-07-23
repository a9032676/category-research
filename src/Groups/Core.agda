{-# OPTIONS --allow-unsolved-metas #-}
module Groups.Core where

open import Level
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym; cong)
open import Data.Nat using (ℕ) renaming (suc to S)

private
  variable
    ℓ : Level

record Group (G : Set ℓ) : Set ℓ where
  infixr 9 _∙_
  field
    𝑒   : G
    _∙_ : G → G → G
    _⁻¹ : G → G
  field
    assocₗ : ∀ 𝑥 𝑦 𝑧 → (𝑥 ∙ 𝑦) ∙ 𝑧 ≡ 𝑥 ∙ (𝑦 ∙ 𝑧)
    assocᵣ : ∀ 𝑥 𝑦 𝑧 → 𝑥 ∙ (𝑦 ∙ 𝑧) ≡ (𝑥 ∙ 𝑦) ∙ 𝑧
    idₗ   : ∀ 𝑥 → 𝑒 ∙ 𝑥 ≡ 𝑥
    idᵣ   : ∀ 𝑥 → 𝑥 ∙ 𝑒 ≡ 𝑥
    invₗ  : ∀ 𝑥 → (𝑥 ⁻¹) ∙ 𝑥 ≡ 𝑒
    invᵣ  : ∀ 𝑥 → 𝑥 ∙ (𝑥 ⁻¹) ≡ 𝑒

record CommutativeGroup (G : Set ℓ) {𝐺 : Group G} : Set ℓ where
  open Group 𝐺 using (_∙_)
  field
    comm : ∀ 𝑥 𝑦 → 𝑥 ∙ 𝑦 ≡ 𝑦 ∙ 𝑥

module GroupProp {G : Set ℓ} (𝐺 : Group G) where

  open Group 𝐺
  
  -- Cancellation
  cancelₗ : (a g h : G) → a ∙ g ≡ a ∙ h → g ≡ h
  cancelₗ a g h p = result
    where
      a⁻¹∙ag≡a⁻¹∙ah : a ⁻¹ ∙ a ∙ g ≡ a ⁻¹ ∙ a ∙ h
      a⁻¹∙ag≡a⁻¹∙ah = cong (a ⁻¹ ∙_) p

      result : g ≡ h
      result
        rewrite
          sym (idₗ g)
          | sym (idₗ h)
          | sym (invₗ a)
          | assocₗ (a ⁻¹) a g
          | assocₗ (a ⁻¹) a h
          = a⁻¹∙ag≡a⁻¹∙ah
  
  cancelᵣ : (a g h : G) → g ∙ a ≡ h ∙ a → g ≡ h
  cancelᵣ a g h p = result
    where
      ga∙a⁻¹≡ha∙a⁻¹ : (g ∙ a) ∙ a ⁻¹ ≡ (h ∙ a) ∙ a ⁻¹
      ga∙a⁻¹≡ha∙a⁻¹ = cong (_∙ a ⁻¹) p

      result : g ≡ h
      result
        rewrite
          sym (idᵣ g)
          | sym (idᵣ h)
          | sym (invᵣ a)
          | assocᵣ g a (a ⁻¹)
          | assocᵣ h a (a ⁻¹)
          = ga∙a⁻¹≡ha∙a⁻¹
  
  _² : (g : G) → G
  g ² = g ∙ g

  _^_ : (g : G) → ℕ → G
  g ^ 0   = 𝑒
  g ^ S n = g ∙ (g ^ n)
  
  data Order (g : G) : Set ℓ where
    finite   : (n : ℕ) (p : g ^ n ≡ 𝑒) → Order g
    infinite : Order g

  ∣_∣=_ : (g : G) (n : ℕ) → G
  ∣_∣=_ g n = g ^ n

open GroupProp using (Order)

test : (G : Set) (g : G) (𝐺 : Group G) → Order 𝐺 g
test G g 𝐺 = {!!}
  where
    open GroupProp 𝐺
