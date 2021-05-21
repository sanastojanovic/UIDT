theory mr17033_Robert_Doza
  imports Main
begin

text‹
  https://www.imo-official.org/problems/IMO2019SL.pdf

  Problem. Let ℤ be the set of integers. Determine all functions f: ℤ ⟶ ℤ such that, for all
  integers a and b,
      f(2a) + 2f(b) = f(f(a + b)).
  Answer: The solutions are f(n) = 0 and f(n) = 2n + K for any constant K ∈ ℤ.
›

lemma lemma1:
  fixes g :: "int ⇒ int"
  assumes "∀a b. g (a + b) = g a + g b"
  fixes n::nat
  shows "g (int n) = (g 1) * (int n)"
  using assms
  apply (induction n)
   apply simp
   apply (smt (verit))
  apply (metis int_distrib(1) mult.commute mult.left_neutral of_nat_Suc)
  done

lemma lemma2:
  fixes g :: "int ⇒ int"
  assumes "∀a b. g (a + b) = g a + g b"
  fixes n::int
  shows "g n = (g 1) * n"
  using assms and lemma1
  apply (induction n)
   apply simp
  apply (metis add_cancel_right_right add_minus_cancel mult_minus_right)
  done

lemma lemma3:
  fixes g :: "int ⇒ int"
  assumes "∀a b. g (a + b) = g a + g b"
  shows "∃ M::int. (∀n. g n = M * n)"
  using assms and lemma2
  by blast

lemma lemma4:
  fixes f :: "int ⇒ int"
  assumes "∃K::int. ∀a b. f a + f b = f(a + b) + K"
  shows "∃(M::int) (K::int). ∀n. f n = M * n + K"
  using lemma3
proof -
  obtain K where "∀a b. f a + f b = f(a + b) + K"
    using assms
    by auto

  define g :: "int ⇒ int" where "∀n. g n = f n - K"
  hence "∀ n. f n = g n + K"
    by auto
  with ‹∀a b. f a + f b = f(a + b) + K› have "∀a b. (g a + K) + (g b + K) = (g (a + b) + K) + K"
    using ‹g ≡ λn. f n - K›
    by fastforce
  hence "∀a b. g a + g b + 2 * K = g (a + b) + 2 * K"
    by auto
  hence "∀a b. g a + g b = g (a + b)"
    by auto
  hence "∀a b. g (a + b) = g a + g b"
    by auto
  hence "∃ M::int. (∀n. g n = M * n)"
    using lemma3
    by blast
  then obtain M where "∀ n. g n = M * n"
    by auto
  with ‹∀n. g n = f n - K› have "∀n. f n - K = M * n"
    by auto
  hence "∀n. f n = M * n + K"
    by (simp add: ‹∀n. f n = g n + K›)
  thus ?thesis
    by auto
qed

lemma lemma5:
  fixes f :: "int ⇒ int"
  assumes "∀(a::int) b. f(2 * a) + 2 * f b = f (f(a + b))"
  shows "∃(K::int). ∀a b. f a + f b = f (a + b) + K"
  using assms
proof -
  let ?K = "f 0"

  from ‹∀(a::int) b. f(2 * a) + 2 * f b = f (f(a + b))› have "∀b. f(2 * 0) + 2 * f b = f (f(0 + b))"
    by blast
  hence "∀b. f 0 + 2 * f b = f (f b)"
    by auto
  hence "∀b. ?K + 2 * f b = f (f b)"
    by auto
  hence 1: "∀b. f (f b) = 2 * f b + ?K"
    by (simp add: add.commute)

  from ‹∀(a::int) b. f(2 * a) + 2 * f b = f (f(a + b))› have "∀a. f(2 * a) + 2 * f 0 = f (f(a + 0))"
    by blast
  hence "∀a. f(2 * a) + 2 * ?K = f (f a)"
    by auto
  with ‹∀b. f (f b) = 2 * f b + ?K› have "∀a. f(2 * a) + 2 * ?K = 2 * f a + ?K"
    by auto
  hence 2: "∀a. f (2 * a) = 2 * f a - ?K"
    by (smt (verit))

  from 1 and 2 have "∀a b. 2 * f a - ?K + 2 * f b = 2 * f (a + b) + ?K"
    using ‹∀(a::int) b. f(2 * a) + 2 * f b = f (f(a + b))›
    by auto
  hence "∀a b. f a + f b = f (a + b) + ?K"
    by (smt (verit, best))
  hence "∃K. ∀a b. f a + f b = f (a + b) + K"
    by auto
  thus ?thesis
    by auto
qed

lemma lemma6:
  fixes f :: "int ⇒ int"
  assumes "∀a b. f(2 * a) + 2 * f b = f (f(a + b))"
  shows "∃(M::int) (K::int). (∀n::int. f n = M * n + K)"
  using assms lemma4 and lemma5
  by simp

theorem
  fixes f :: "int ⇒ int"
  assumes "∀a b. f(2 * a) + 2 * f b = f (f(a + b))"
  shows "(∃ K. (∀ n. f n = 2 * n + K)) ∨ (∀ n. f n = 0)"
  using lemma6
proof -
  have "∃(M::int) (K::int). (∀n::int. f n = M * n + K)"
    using assms
    using lemma6
    by auto
  then obtain M::int and K::int where "∀n::int. f n = M * n + K"
    by auto

  have "M = 2 ∨ M ≠ 2"
    by auto
  thus ?thesis
  proof
    assume "M = 2"
    show ?thesis
      by (simp add: ‹(M::int) = (2::int)› ‹∀n::int. (f::int ⇒ int) n = (M::int) * n + (K::int)›)
  next
    assume "M ≠ 2"

    have "∀ a b::int. f(2 * a) + 2 * f b = f (M * (a + b) + K)"
      using ‹∀a b. f(2 * a) + 2 * f b = f (f(a + b))› and ‹∀n::int. f n = M * n + K›
      by fastforce
    with ‹∀n::int. f n = M * n + K› have "∀ a b::int. f(2 * a) + 2 * f b = M * (M * (a + b) + K) + K"
      by fastforce
    with ‹∀n::int. f n = M * n + K› have "∀ a b::int. f(2 * a) + 2 * (M * b + K) = M * (M * (a + b) + K) + K"
      by fastforce
    with ‹∀n::int. f n = M * n + K› have "∀ a b::int. (M * (2 * a) + K) + 2 * (M * b + K) = M * (M * (a + b) + K) + K"
      by fastforce
    hence "∀ a b::int. M * 2 * a + K + 2 * M * b + 2 * K = M * M * (a + b) + M * K + K"
      by (simp add: field_simps)
    hence "∀ a b::int. M * 2 * a + 2 * M * b + 2 * K = M * M * (a + b) + M * K"
      by (simp add: field_simps)
    hence "∀ a b::int. 2 * M * a + 2 * M * b + 2 * K = M * M * (a + b) + M * K"
      by (simp add: field_simps)
    hence "∀ a b::int. 2 * M * (a + b) + 2 * K = M * M * (a + b) + M * K"
      by (simp add: field_simps)
    hence "∀ a b::int. 2 * M * (a + b) - M * M * (a + b) = M * K - 2 * K"
      by (simp add: field_simps)
    hence "∀ a b::int. (2 - M) * M * (a + b) = (M - 2) * K"
      by (simp add: field_simps)
    hence "∀ a b::int. (2 - M) * M * (a + b) + (2 - M) * K = 0"
      by (simp add: field_simps)
    hence "∀ a b::int. (2 - M) * M * (a + b) + (2 - M) * K = 0"
      by (simp add: field_simps)
    hence "∀ a b::int. (2 - M) * (M * (a + b) + K) = 0"
      by (simp add: field_simps)
    with ‹M ≠ 2› have "∀ a b::int. M * (a + b) + K = 0"
      by fastforce
    hence "K = 0"
      by (metis add.commute add.right_neutral mult_zero_right)
    with ‹∀ a b::int. M * (a + b) + K = 0› have "M = 0"
      by (metis add.right_neutral mult.right_neutral)

    from ‹∀n::int. f n = M * n + K› and ‹M = 0› and ‹K = 0› have "∀ n. f n = 0"
      by auto
    thus ?thesis
      by auto
  qed
qed

end