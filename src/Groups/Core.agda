{-# OPTIONS --allow-unsolved-metas #-}
module Groups.Core where

open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym; cong)
open import Level

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
    idₗ   : ∀ 𝑥 → 𝑥 ∙ 𝑒 ≡ 𝑥
    idᵣ   : ∀ 𝑥 → 𝑒 ∙ 𝑥 ≡ 𝑥
    invₗ  : ∀ 𝑥 → 𝑥 ∙ (𝑥 ⁻¹) ≡ 𝑒
    invᵣ  : ∀ 𝑥 → (𝑥 ⁻¹) ∙ 𝑥 ≡ 𝑒

record CommutativeGroup (G : Set ℓ) {𝐺 : Group G} : Set ℓ where
  open Group 𝐺 using (_∙_)
  field
    comm : ∀ 𝑥 𝑦 → 𝑥 ∙ 𝑦 ≡ 𝑦 ∙ 𝑥

module GroupProp {G : Set ℓ} {𝐺 : Group G} where

  open Group 𝐺
  
  -- Cancellation
  cancelₗ : (a g h : G) → g ∙ a ≡ h ∙ a → g ≡ h
  cancelₗ a g h p = {!!}
  
  cancelᵣ : (a g h : G) → a ∙ g ≡ a ∙ h → g ≡ h
  cancelᵣ a g h p = {!!}
