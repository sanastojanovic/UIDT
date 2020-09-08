theory mi16144_Nikoleta_Vukajlovic
  imports Complex_Main
begin

text\<open>
  Prvi dan, zadatak 2 na linku: https://imomath.com/srb/zadaci/1995_mmo_resenja.pdf

  Neka su a, b, c pozitivni realni brojevi sa a*b*c= 1. Dokazati nejednakost
  1/(a^3 * (b + c)) + 1/(b^3 * (a + c)) + 1/(c^3 * (a + b)) \<ge> 3/2.
 \<close>

text\<open>Smena x = 1 / a\<close>

lemma smena:
  fixes a::real
  assumes "a > 0" "x = 1 / a"
  shows "a = 1 / x"
  using assms
proof-
  have "1 = x * a"
    using assms
    by auto
  then show ?thesis
    using assms
    by auto
qed


text\<open>Uslov nakon uvodjenja smene postaje :  x * y * z = 1\<close>

lemma uslov_posle_smene:
  fixes a b c::real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1" "x = 1 / a" "y = 1 / b" "z = 1 / c"
  shows "x * y * z = 1"
  using assms
proof-
  have "a = 1 / x"
    using assms(1) assms(5) smena
    by blast
  have "b = 1 / y"
    using assms(2) assms(6) smena
    by blast
  have "c = 1 / z"
    using assms(3) assms(7) smena
    by blast
  then have "a * b * c = 1 / x * 1 / y * 1 / z"
    using `a = 1/ x` `b = 1 / y` `c = 1 / z`
    by auto
  then have "1 / x * 1 / y * 1 / z = 1"
    using assms
    by auto
  then have "x * y * z * (1 / x * 1 / y * 1 / z) = x * y * z"
    by auto
  then have "1 = x * y * z"
    using \<open>1 / x * 1 / y * 1 / z = 1\<close> 
    by auto
  then show ?thesis
    by auto
qed

lemma sabiranje_razlomaka[simp]:
  fixes a b::real
  assumes "a > 0" "b > 0"
  shows "1 / a + 1 / b = (b + a) / (a * b)"
  using assms
proof-
  have "1 / a + 1 / b = b / (b * a) + a / (a * b)"
    using assms
    by simp
  also have "... = (b + a) / (a * b)"
    using assms
    by (metis Groups.mult_ac(2) add_divide_distrib)
  finally show ?thesis
    by simp
qed

text\<open>Leva strana nejednakosti nakon uvodjenja smene postaje :
    (x ^ 2) / (y + z) + (y ^ 2) / (x + z) + (z ^ 2) / (x + y)\<close>

lemma leva_strana_nakon_smene:
  fixes x y z :: real
  assumes "a * b * c = 1" "x = 1 / a" "y = 1 / b" "z = 1 /c" "a > 0" "b > 0" "c > 0" "x * y * z = 1"
  shows "1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)) =
        (x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)"
  using assms
proof-
  have "a = 1 / x"
    using assms smena
    by blast
  have "b = 1 / y"
    using assms smena
    by blast
  have "c = 1 / z"
    using assms smena
    by blast
  have "1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)) = 
        1 / (((1 / x) ^ 3) * (1 / y + 1 / z)) +
        1 / (((1 / y) ^ 3) * (1 / x + 1 / z)) +
        1 / (((1 / z) ^ 3) * (1 / x + 1 / y))"
    using assms smena
    by presburger
  also have "... =
            (x ^ 3) / (1 / y + 1 / z) +
            (y ^ 3) / (1 / x + 1 / z) +
            (z ^ 3) / (1 / x + 1 / y)"
    using assms `a = 1 / x` `b = 1 / y` `c = 1 / z`
    by (metis (mono_tags, lifting) divide_divide_eq_left power_one_over)
  also have "... =
            (x ^ 3) / (z / (z * y) + y / (z * y)) +
            (y ^ 3) / (z / (z * x) + x / (z * x)) +
            (z ^ 3) / (y / (x * y) + x / (x * y))"
    using assms smena
    by force
  also have "... =
             (x ^ 3) / ((z + y) / (z * y)) +
             (y ^ 3) / (z / (z * x) + x / (z * x)) +
            (z ^ 3) / (y / (x * y) + x / (x * y))"
    using assms sabiranje_razlomaka[of "z" "y"]
    by simp
  also have "... =
             (x ^ 3) / ((z + y) / (z * y)) +
             (y ^ 3) / ((z + x) / (z * x)) +
            (z ^ 3) / (y / (x * y) + x / (x * y))"
    using assms sabiranje_razlomaka[of "z" "x"]
    by simp
    also have "... =
             (x ^ 3) / ((z + y) / (z * y)) +
             (y ^ 3) / ((z + x) / (z * x)) +
             (z ^ 3) / ((x + y) / (x * y))"
    using assms sabiranje_razlomaka[of "x" "y"]
    by simp
  also have "... =
            (x ^ 3 * (z * y)) / (z + y) +
            (y ^ 3 * (z * x)) / (z + x) +
            (z ^ 3 * (x * y)) / (x + y)"
    using assms
    by simp
  also have "... =
            (x ^ 2 * x * z * y) / (z + y) +
            (y ^ 2 * y * z * x) / (z + x) +
            (z ^ 2 * z * x * y) / (x + y)"
    using assms
    by (simp add: power3_eq_cube semiring_normalization_rules(29))
  also have "... =
            (x ^ 2 * x * y * z) / (z + y) +
            (y ^ 2 * x * y * z) / (z + x) +
            (z ^ 2 * x * y * z) / (x + y)"
    using assms
    by (metis (no_types, lifting) semiring_normalization_rules(16))
  also have "... =
          (x ^ 2) / (z + y) +
          (y ^ 2) / (z + x) +
          (z ^ 2) / (x + y)"
    using assms
    by simp
  finally show ?thesis
    using assms  `a = 1 / x` `b = 1 / y` `c = 1 / z`
    by blast
qed

lemma Kosi_Svarcova_nejednakost:
  fixes x y z :: real
  shows "(sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
         ((x / sqrt(z + y)) ^ 2 + 
          (y / sqrt(z + x)) ^ 2 + 
          (z / sqrt(x + y)) ^ 2) \<ge>
        (sqrt(y + z) * (x / sqrt(z + y)) + 
             sqrt(z + x) * (y / sqrt(z + x)) +
             sqrt(x + y) * (z / sqrt(x + y))) ^ 2"
  sorry

lemma kvadrat_korena:
  fixes x y :: real
  assumes "x > 0" "y > 0" 
  shows "x + y = sqrt(x + y) ^ 2"
  using assms(1) assms(2) by auto

lemma kvadrat:
  fixes x y z :: real
  shows "(x ^ 2) / (sqrt(y + z) ^ 2) = (x / sqrt(y + z)) ^ 2"
  by (simp add: power_divide)

lemma skracivanje:
  fixes y z x :: real
  assumes "y > 0" "z > 0"
  shows "sqrt(y + z) * (x / sqrt(y + z)) = x"
  using assms(1) assms(2) by auto

lemma nejednakost_nakon_Kosi_Svarca:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "((y+z) + (z+x) + (x+y)) * 
         ((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)) \<ge>
         (x + y + z) ^ 2"
proof-
  have "((y+z) + (z+x) + (x+y)) * 
         ((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)) =
        (sqrt(y+z) ^ 2 + (z + x)  + (x+y)) *
        ((x ^ 2) /(z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y))"
    using assms kvadrat_korena[of y z]
    by auto
  also have "... =
        (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + (x+y)) *
        ((x ^ 2) /(z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y))"
    using assms kvadrat_korena[of z x]
    by auto
  also have "... =
        (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
        ((x ^ 2) /(z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y))"
    using assms kvadrat_korena[of x y]
    by auto
  also have "... =
        (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
        ((x ^ 2) /(sqrt(z + y) ^ 2) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y))"
    using assms kvadrat_korena[of z y]
    by auto
  also have "... =
        (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
        ((x ^ 2) /(sqrt(z + y) ^ 2) + (y ^ 2) / (sqrt(z + x) ^ 2) + (z ^ 2) / (x + y))"
    using assms kvadrat_korena[of z x]
    by auto
  also have "... =
        (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
         ((x ^ 2) / (sqrt(z + y) ^ 2) + 
          (y ^ 2) / (sqrt(z + x) ^ 2) + 
          (z ^ 2) / (sqrt(x + y) ^ 2))"
    using assms kvadrat_korena[of x y]
    by auto
  also have "... =
         (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
         ((x / sqrt(z + y)) ^ 2 + 
          (y ^ 2) / (sqrt(z + x) ^ 2) + 
          (z ^ 2) / (sqrt(x + y) ^ 2))"
    using assms kvadrat[of x z y]
    by simp
  also have "... =
         (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
         ((x / sqrt(z + y)) ^ 2 + 
          (y / sqrt(z + x)) ^ 2 + 
          (z ^ 2) / (sqrt(x + y) ^ 2))"
    using assms kvadrat[of y z x]
    by simp
  also have "... =
         (sqrt(y+z) ^ 2 + sqrt(z + x) ^ 2  + sqrt(x+y) ^ 2) *
         ((x / sqrt(z + y)) ^ 2 + 
          (y / sqrt(z + x)) ^ 2 + 
          (z / sqrt(x + y)) ^ 2)"
    using assms kvadrat[of z x y]
    by simp 
  also have "... \<ge> 
            (sqrt(y + z) * (x / sqrt(y + z)) + 
             sqrt(z + x) * (y / sqrt(z + x)) +
             sqrt(x + y) * (z / sqrt(x + y))) ^ 2"
    using assms Kosi_Svarcova_nejednakost[of x y z]
    by smt
  also have "... \<ge> (x + y + z) ^ 2"
    using assms skracivanje[of y z x]
    using \<open>(sqrt (y + z) * (x / sqrt (y + z)) + sqrt (z + x) * (y / sqrt (z + x)) + sqrt (x + y) * (z / sqrt (x + y)))\<^sup>2 \<le> ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * ((x / sqrt (z + y))\<^sup>2 + (y / sqrt (z + x))\<^sup>2 + (z / sqrt (x + y))\<^sup>2)\<close> by auto
  then show ?thesis 
    using \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * ((x / sqrt (z + y))\<^sup>2 + (y / sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * ((x / sqrt (z + y))\<^sup>2 + (y / sqrt (z + x))\<^sup>2 + (z / sqrt (x + y))\<^sup>2)\<close> \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * ((x / sqrt (z + y))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * ((x / sqrt (z + y))\<^sup>2 + (y / sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2)\<close> \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (sqrt (z + y))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * ((x / sqrt (z + y))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2)\<close> \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (sqrt (z + y))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (x + y)) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (sqrt (z + y))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (sqrt (x + y))\<^sup>2)\<close> \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (sqrt (z + y))\<^sup>2 + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (sqrt (z + y))\<^sup>2 + y\<^sup>2 / (sqrt (z + x))\<^sup>2 + z\<^sup>2 / (x + y))\<close> \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (sqrt (z + y))\<^sup>2 + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y))\<close> \<open>((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (sqrt (x + y))\<^sup>2) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y))\<close> \<open>((sqrt (y + z))\<^sup>2 + (z + x) + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)) = ((sqrt (y + z))\<^sup>2 + (sqrt (z + x))\<^sup>2 + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y))\<close> \<open>(y + z + (z + x) + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)) = ((sqrt (y + z))\<^sup>2 + (z + x) + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y))\<close> 
    by presburger
qed

lemma pomocna:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  assumes "x * y \<ge> z"
  shows "y \<ge> z / x"
  by (smt assms(1) assms(4) divide_right_mono nonzero_mult_div_cancel_left)

lemma pomocna2:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x + y + z) * (x + y + z) / (2 * (x + y + z)) \<ge>(x + y + z)/2"
  using assms
proof-
  have "(x + y + z) * (x + y + z) / (2 * (x + y + z)) \<ge>
        (1 / 2) * ((x + y + z) * (x + y + z))/(x + y + z)"
     using assms
    by (simp add: add_divide_distrib)
  then have "... \<ge> (1/2) * (x + y + z)"
    using assms
    by (metis divide_eq_0_iff eq_divide_imp mult.assoc mult_eq_0_iff)
  then show ?thesis
    by auto
qed
  

lemma kraci_oblik:
  fixes x y z :: real
  assumes "x > 0" "y > 0" "z > 0" "x * y * z = 1"
  shows "(((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y))) \<ge> (x + y + z)/2"
proof-
  have "((y + z) + (z + x) + (x + y)) * 
         ((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)) \<ge>
         (x + y + z) ^ 2"
    using assms nejednakost_nakon_Kosi_Svarca[of x y z]
    by blast
  have "(2 * x + 2 * y + 2 * z) *
            ((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)) \<ge>
            ((x + y + z) ^ 2)"
    by (smt \<open>(x + y + z)\<^sup>2 \<le> (y + z + (z + x) + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y))\<close>)
  have " ((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)) \<ge>
        ((x + y + z) ^ 2) / (2 * x + 2 * y + 2 * z) "
    using assms pomocna
    by (smt \<open>(x + y + z)\<^sup>2 \<le> (y + z + (z + x) + (x + y)) * (x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y))\<close> divide_right_mono nonzero_mult_div_cancel_left)
  then have "... \<ge> (x + y + z) * (x + y + z) / (2 * (x + y + z))"
    using assms
    by (simp add: \<open>(x + y + z)\<^sup>2 / (2 * x + 2 * y + 2 * z) \<le> x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)\<close> semiring_normalization_rules(29))
  then have "... \<ge> (1/2) * (x + y + z)"
    using assms pomocna2[of x y z]
    using \<open>(x + y + z) * (x + y + z) / (2 * (x + y + z)) \<le> x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)\<close> 
    by linarith
  then show ?thesis
    using assms
    using \<open>((x ^ 2) / (z + y) + (y ^ 2) / (z + x) + (z ^ 2) / (x + y)) \<ge>
        ((x + y + z) ^ 2) / (2 * x + 2 * y + 2 * z) \<close>
    using \<open>(x + y + z) * (x + y + z) / (2 * (x + y + z)) \<le> x\<^sup>2 / (z + y) + y\<^sup>2 / (z + x) + z\<^sup>2 / (x + y)\<close>
    by linarith
qed

lemma nejednakost_sredina:
  fixes x y z :: real
  shows "(x + y + z) / 3 = sqrt3(x * y * z)"
  sorry

lemma 
  fixes x y z :: real
  assumes "x = 1" "y = 1" "z = 1"
  shows "(x + y + z) / 2 \<ge> (3/2)"
proof-
  have "(x + y + z) / 2 = ((x + y + z) / 2) * (3/3)"
    by simp
  then have "... = ((x + y + z) / 3) * (3/2)"
    by simp
  then have "... \<ge> sqrt3(x * y * z) * (3/2)"
    using nejednakost_sredina
    by simp
  then show ?thesis
    using assms
    by simp
qed

lemma zadatak:
  fixes a b c :: real
  assumes "a > 0" "b > 0" "c > 0" "a * b * c = 1"
  shows "1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)) \<ge> 3/2"
  sorry

end