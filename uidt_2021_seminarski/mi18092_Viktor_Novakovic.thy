theory mi18092_Viktor_Novakovic
  imports Complex_Main
begin

text\<open>
https://www.imo-official.org/problems/IMO2018SL.pdf

A5

Determine all funtions f : (0, inf) => R satisfying
ˆ
(x + 1/x)f(y) = f(xy) + f(y/x)                                                        (1)

for all x, y > 0.



Answer: f(x) = C1*x + C2/x with arbitrary constants C1 and C2.
\<close>


text\<open>
Solution 1. Fix a real number a ą 1, and take a new variable t. 
For the values f(t), f(t^2), f(at) and f(a^2*t^2), 
the relation (1) provides a system of linear equations:



x = y = t:

(t + 1/t)f(t) = f(t^2) + f(1)                                                         (2a)
\<close>

lemma lemma2a:
  fixes t::real
  fixes f::"real\<Rightarrow>real"
  assumes "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(t + 1/t) * (f t) = f (t^2) + f 1"
proof -
  have "(t + 1/t) * (f t) = f (t*t) + f (t/t)"
    using assms by simp
  then show "(t + 1/t) * (f t) = f (t^2) + f 1"
    using assms
    by (smt (verit) divide_eq_1_iff power2_eq_square)
qed


text\<open>
x = t/a, y = at:

(t/a + a/t)f(at) = f(t^2) + f(a^2)                                                    (2b)
\<close>


lemma lemma2b:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(t/a + a/t) * (f (a*t)) = f (t^2) + f (a^2)"
proof -

  have "(t/a + a/t) * (f (a*t)) = ((t/a) + 1/(t/a)) * (f (a*t))"
    using assms by simp
  also have "\<dots> = f ((t/a)*(a*t)) + f ((a*t)/(t/a))"
    using assms
    by (smt (z3) divide_divide_eq_left' divide_pos_pos divide_self_if mult.commute
        mult_cancel_right mult_cancel_right2 mult_imp_less_div_pos times_divide_eq_left)
  also have "\<dots> = f (t*t) + f (a*t/t*a)"
    using assms by auto
  also have "\<dots> = f (t^2) + f (a^2)"
    using assms
    by (smt (z3) nonzero_eq_divide_eq power2_eq_square)

  finally show ?thesis.

qed


text\<open>
x = a^2t, y = t:

(a^2t + a/(a^2t))f(t) = f(a^2t^2) + f(1/a^2)                                          (2c)
\<close>

lemma lemma2c:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(a^2*t + 1/(a^2*t)) * (f t) = f (a^2*t^2) + f (1/a^2)"
proof -

  have "(a^2*t + 1/(a^2*t)) * (f t) = f ((a^2*t)*t) + f (t/(a^2*t))"
    using assms by simp
  then show  "(a^2*t + 1/(a^2*t)) * (f t) = f (a^2*t^2) + f (1/a^2)"
    using assms
    by (smt (verit) nonzero_divide_mult_cancel_right 
        nonzero_mult_div_cancel_left numeral_One power2_eq_square 
        power_add_numeral2 power_mult_distrib power_one_right semiring_norm(2) 
        times_divide_eq_right zero_eq_power2)
qed



text\<open>
x = at, y = at:

(at + a/(at))f(at) = f(a^2t^2) + f(1)                                                 (2d)
\<close>

lemma lemma2d:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(a*t + 1/(a*t)) * (f (a*t)) = f (a^2*t^2) + f 1"
  by (smt (verit) assms(1) assms(2) assms(3) lemma2a lemma2c mult_pos_pos power_mult_distrib)


text\<open>
In order to eliminate f(t^2), take the difference of (2a) and (2b); 
from (2c) and (2d) eliminate f(a^2t^2); then by taking a linear combination, 
eliminate f(at) as well:

(t+1/t)f(t) - (t/a + a/t)f(at) = f(1) - f(a^2)    and

(a^2t + 1/(a^2t))f(t) - (at + 1/at)f(at) = f(1/a^2) - f(1), so

((at + 1/at)(t + 1/t) - (t/a + a/t)(a^2t + 1/(a^2t)))f(t) =
                      = (at + 1/at) (f(1) - f(a^2)) - (t/a + a/t)(f(1/a^2) - f(1))
\<close>


lemma lemma2a2b:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) = f 1 - (f (a^2))"
  by (simp add: assms(1) assms(2) assms(3) lemma2a lemma2b)


lemma lemma2c2d:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)) = f(1/a^2) - f 1"
proof -

  have "(a^2*t + 1/(a^2*t)) * (f t) = f (a^2*t^2) + f (1/a^2)"
    using assms lemma2c by auto

  moreover

  have "(a*t + 1/(a*t)) * (f (a*t)) = f (a^2*t^2) + f 1"
    using assms lemma2d by auto

  ultimately

  have "(a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)) 
        = f (a^2*t^2) + f (1/a^2) - (f (a^2*t^2) + f 1)"
    using assms by auto

  then show ?thesis by auto
qed


lemma lemma_help_1:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1))"
proof -
  have "(t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) = f 1 - (f (a^2))"
    using assms lemma2a2b by simp

  moreover 
  
  have "(a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)) = f(1/a^2) - f 1"
    using assms lemma2c2d by simp

  ultimately

  have "(t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)))
        = f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1)"
    by simp


  then show "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1))"
    by simp

qed

lemma lemma_help_2:
  fixes t::real
  fixes a::real
  assumes "a > 1" "t > 0"
  shows "(a*t + 1/(a*t))/(a*t + 1/(a*t)) = 1"
  by (metis add_nonpos_eq_0_iff add_pos_pos assms(1) assms(2) div_0 div_self
      divide_le_0_1_iff less_numeral_extra(3) nonzero_eq_divide_eq
      not_one_less_zero verit_comp_simplify1(3))


lemma lemma_help_3:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = ((a*t + 1/(a*t))*(t + 1/t) - (t/a + a/t)*(a^2*t + 1/(a^2*t))) * (f t)"
proof -

  have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*(((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)))
        - ((t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)))))"
    by simp

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)))
        - (a*t + 1/(a*t)) * ((t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t))          
        * (f t) - (a*t + 1/(a*t)) * (f (a*t))))"
    using right_diff_distrib' by blast

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)))
        - (a*t + 1/(a*t)) * (((t/a + a/t)*(((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) 
        * (f (a*t))))))/(a*t + 1/(a*t))"
    by fastforce

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)))
        - (a*t + 1/(a*t))/(a*t + 1/(a*t)) * (((t/a + a/t)*(((a^2*t + 1/(a^2*t)) * (f t) 
        - (a*t + 1/(a*t)) * (f (a*t))))))"
    by simp

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*(((t + 1/t) * (f t)) - ((t/a + a/t) * (f (a*t))))
        - ((t/a + a/t)*(((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)))))"
    using assms(1) assms(2) lemma_help_2 by auto

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*((t + 1/t) * (f t)) - (a*t + 1/(a*t))*((t/a + a/t) * (f (a*t)))
        - ((t/a + a/t)*(((a^2*t + 1/(a^2*t)) * (f t)) - ((a*t + 1/(a*t)) * (f (a*t)))))"
    using right_diff_distrib by auto

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = (a*t + 1/(a*t))*((t + 1/t) * (f t)) - (a*t + 1/(a*t))*((t/a + a/t) * (f (a*t)))
        - ((t/a + a/t)*((a^2*t + 1/(a^2*t)) * (f t)) - (t/a + a/t)*((a*t + 1/(a*t)) * (f (a*t))))"
    by (simp add: right_diff_distrib)

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = ((a*t + 1/(a*t))*((t + 1/t) * (f t))) - ((t/a + a/t) *(a*t + 1/(a*t))* (f (a*t)))
        - ((t/a + a/t)*((a^2*t + 1/(a^2*t)) * (f t))) + ((t/a + a/t)*((a*t + 1/(a*t)) * (f (a*t))))"
    by simp

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)))) 
        = (a*t + 1/(a*t))*((t + 1/t) * (f t)) - (t/a + a/t)*((a^2*t + 1/(a^2*t)) * (f t))
        + ((t/a + a/t)*((a*t + 1/(a*t)) * (f (a*t)))) - ((t/a + a/t) *(a*t + 1/(a*t))* (f (a*t)))"
    by force

  then have "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t))))
        = ((a*t + 1/(a*t))*((t + 1/t)) * (f t)) - ((t/a + a/t)*(a^2*t + 1/(a^2*t)) * (f t))"
    by simp
  
  then show "(a*t + 1/(a*t))*((t + 1/t) * (f t) - (t/a + a/t) * (f (a*t)) 
        - (t/a + a/t)/(a*t + 1/(a*t))*((a^2*t + 1/(a^2*t)) * (f t) - (a*t + 1/(a*t)) * (f (a*t)))) 
        = ((a*t + 1/(a*t))*(t + 1/t) - (t/a + a/t)*(a^2*t + 1/(a^2*t))) * (f t)"
    by (simp add: left_diff_distrib')

qed

lemma lemma_help_4:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "(a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1))
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2))) - (t/a + a/t)*(f(1/a^2) - f 1)"
proof -

  have "(a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1))
        = (a*t + 1/(a*t)) * ((f 1 - (f (a^2))) - ((t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1)))"
    by simp

  then have "(a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1)) 
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2))) 
        - (a*t + 1/(a*t)) * ((t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1))"
    using right_diff_distrib' by blast

  then have "(a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1))
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2))) 
        - ((a*t + 1/(a*t)) * ((t/a + a/t)*(f(1/a^2) - f 1))/(a*t + 1/(a*t)))"
    by simp

  then have "(a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1)) 
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2))) 
        - ((a*t + 1/(a*t)) /(a*t + 1/(a*t)) * ((t/a + a/t)*(f(1/a^2) - f 1)))"
    by simp

  then show  "(a*t + 1/(a*t)) * (f 1 - (f (a^2)) - (t/a + a/t)/(a*t + 1/(a*t))*(f(1/a^2) - f 1)) 
        = (a*t + 1/(a*t)) * (f 1 - (f (a^2))) - (t/a + a/t)*(f(1/a^2) - f 1)"
    using assms(1) assms(2) lemma_help_2 by auto

qed



lemma lemma_lose_f_at:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "((a*t + 1/(a*t))*(t+1/t) - (t/a + a/t)*(a^2*t + 1/(a^2*t)))*(f t) 
              = (a*t + 1/(a*t))*(f 1 - f (a^2)) - (t/a + a/t) * (f (1/a^2) - f 1)"
  using assms lemma_help_1 lemma_help_3 lemma_help_4 by presburger



text\<open>
Notice that on the left-hand side, the coefficient of f(t) is nonzero and does not depend on t:

(at + 1/(at))*(t + 1/t) - (t/a + a/t)*(a^2t + 1/(a^2t)) = a + 1/a - (a^3 + 1/a^3) < 0

After dividing by this fixed number, we get

f(t) = C1t + C2/t                                                                     (3)

where the numbers C1 and C2 are expressed in terms of a, f(1), f(a^2) and f(1/a^2), and
the do not depend on t.
\<close>

lemma lemma_left_side:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "((a*t + 1/(a*t))*(t+1/t) - (t/a + a/t)*(a^2*t + 1/(a^2*t))) = a + 1/a - (a^3 + 1/(a^3))"
proof -

  have "((a*t + 1/(a*t))*(t+(1/t)) - ((t/a + a/t)*((a^2*t) + (1/(a^2*t))))) 
        = (((a*t) + (1/(a*t)))*t) + (((a*t) + 1/(a*t))*(1/t)) 
        - ((((t/a) + (a/t))*(a^2*t)) + (((t/a) + (a/t))*(1/(a^2*t))))"
    by (simp add: ring_class.ring_distribs(1))


  also have "\<dots> = ((a*t)*t + (1/(a*t))*t) + ((a*t)*(1/t) + 1/(a*t)*(1/t)) 
        - (((t/a)*(a^2*t) + (a/t)*(a^2*t)) + ((t/a)*(1/(a^2*t)) + (a/t)*(1/(a^2*t))))"
    by (metis (no_types, hide_lams) ring_class.ring_distribs(2))

  also have "\<dots> = a*t*t + 1/a/t*t  + a*t/t + 1/a/t/t
        - t/a*a^2*t - a/t*a^2*t - t/a/a^2/t - a/t/(a^2)/t"
    by simp

  also have "\<dots> = a*t*t + 1/a  + a + 1/a/t/t
        - t*t/a*a^2 - a*a^2 - 1/a/a^2 - 1/t/a^2*a/t"
    using assms by auto

  also have "\<dots> = a*t*t + 1/a  + a + 1/a/t/t
        - t*t/a*a*a - a*a*a - 1/(a*a*a) - 1/t/a/a*a/t"
    by (simp add: power2_eq_square)

  also have "\<dots> = a*t*t + 1/a + a + 1/a/t/t - t*t*a - a*a*a - 1/(a*a*a) - 1/t/a/t"
    by fastforce

  also have "\<dots> = a*t*t + 1/a + a + 1/a/t/t - a*t*t - a*a*a - 1/(a*a*a) - 1/a/t/t"
    by simp

  also have "\<dots> = 1/a + a  - a*a*a - 1/(a*a*a)"
    by simp

  finally show "((a*t + 1/(a*t))*(t+1/t) - (t/a + a/t)*(a^2*t + 1/(a^2*t)))
             = a + 1/a - (a^3 + 1/(a^3))"
    by (simp add: power3_eq_cube)

qed


lemma lemma_left_smaller_than_zero:
  fixes a::real
  assumes "a>1"
  shows "a + 1/a - (a^3 + 1/(a^3)) < 0"
proof - 

  have "a < a^3"
    by (smt (z3) assms(1) numeral_le_one_iff power_le_imp_le_exp 
        power_one_right semiring_norm(70))

  have "1/a  > 1/(a^3)"
    by (smt (z3) assms divide_less_eq_1_pos one_less_numeral_iff 
        power_one_over power_one_right power_strict_decreasing_iff 
        semiring_norm(77) zero_less_divide_1_iff)

  then have "1/a - 1/(a^3) > 0"
    by simp

  moreover 
  
  have "a^4 > 1"
    using assms by auto

  ultimately

  have "1/a - 1/(a^3) < (a^4*(1/a - 1/(a^3)))"
    by simp

  have "a^4*(1/a - 1/a^3) = a^4*1/a - a^4*1/a^3"
    by (simp add: right_diff_distrib')

  also have "\<dots> = a^3 - a"
    by (simp add: power3_eq_cube power4_eq_xxxx)

  then have "1/a - 1/a^3 < a^3 - a"
    using \<open>1 / a - 1 / a ^ 3 < a ^ 4 * (1 / a - 1 / a ^ 3)\<close> calculation by auto

  then have "a + 1/a - a^3 - 1/a^3 < 0"
    by auto

  then show ?thesis by auto 
qed



lemma lemma_divide_left:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "a > 1" "t > 0" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "f t = (a*(f 1 - f (a^2)) - (f (1/a^2) - f 1)/a)/(a + 1/a - (a^3 + 1/(a^3)))*t
          + ((f 1 - f (a^2))/a - a*(f (1/a^2) - f 1))/(a + 1/a - (a^3 + 1/(a^3)))/t "
proof - 

  have "((((a*(f 1 - f (a^2))) - ((f (1/a^2) - f 1)/a))*t)
        + (((f 1 - f (a^2))/a) - (a*(f (1/a^2) - f 1)))/t)
        = (((a*(f 1 - f (a^2)))*t - ((f (1/a^2) - f 1)/a)*t)
        + (((f 1 - f (a^2))/a)/t - (a*(f (1/a^2) - f 1))/t))"
    by (simp add: diff_divide_distrib left_diff_distrib)


  have "((a*t + 1/(a*t))*(t+1/t) - (t/a + a/t)*(a^2*t + 1/(a^2*t)))*(f t) 
        = (a*t + 1/(a*t))*(f 1 - f (a^2)) - (t/a + a/t) * (f (1/a^2) - f 1)"
    using assms lemma_lose_f_at by simp

  then have "(a + 1/a - (a^3 + 1/(a^3)))*(f t) 
        = (a*t + 1/(a*t))*(f 1 - f (a^2)) - (t/a + a/t) * (f (1/a^2) - f 1)"
    using assms lemma_left_side by simp

  then have "(a + 1/a - (a^3 + 1/(a^3)))/(a + 1/a - (a^3 + 1/(a^3)))*(f t) 
        = ((a*t + 1/(a*t))*(f 1 - f (a^2)) - (t/a + a/t) * (f (1/a^2) - f 1))
        /(a + 1/a - (a^3 + 1/(a^3)))"
    using assms by (metis times_divide_eq_left)

  then have "f t = (((a*t) + (1/(a*t)))*(f 1 - f (a^2)) - (((t/a) + (a/t)) * (f (1/a^2) - f 1)))
        /(a + 1/a - (a^3 + 1/(a^3)))"
    by (smt (verit) assms(1) eq_divide_imp
        lemma_left_smaller_than_zero nonzero_divide_mult_cancel_left 
          right_inverse_eq zero_eq_1_divide_iff)

  also have "\<dots> = (a*(f 1 - f (a^2))*t + (f 1 - f (a^2))/a/t 
        - (f (1/a^2) - f 1)/a*t - a*(f (1/a^2) - f 1)/t)
        /(a + 1/a - (a^3 + 1/(a^3)))"
    by (simp add: ring_class.ring_distribs(2))

  also have "\<dots> = (((a*(f 1 - f (a^2)))*t - ((f (1/a^2) - f 1)/a)*t)
        + (((f 1 - f (a^2))/a)/t - (a*(f (1/a^2) - f 1))/t))
        /(a + 1/a - (a^3 + 1/(a^3)))"
    by simp

  also have "\<dots> = (((a*(f 1 - f (a^2)) - (f (1/a^2) - f 1)/a)*t)
        + (((f 1 - f (a^2))/a - a*(f (1/a^2) - f 1))/t))
        /(a + 1/a - (a^3 + 1/(a^3)))"
    using \<open>(a * (f 1 - f (a\<^sup>2)) - (f (1 / a\<^sup>2) - f 1) / a) * t 
        + ((f 1 - f (a\<^sup>2)) / a - a * (f (1 / a\<^sup>2) - f 1)) / t 
        = a * (f 1 - f (a\<^sup>2)) * t - (f (1 / a\<^sup>2) - f 1) / a * t 
        + ((f 1 - f (a\<^sup>2)) / a / t - a * (f (1 / a\<^sup>2) - f 1) / t)\<close> by presburger

  also have "\<dots> = (a*(f 1 - f (a^2)) - (f (1/a^2) - f 1)/a)*t/(a + 1/a - (a^3 + 1/(a^3)))
        + ((f 1 - f (a^2))/a - a*(f (1/a^2) - f 1))/t/(a + 1/a - (a^3 + 1/(a^3)))"
    by (simp add: add_divide_distrib)

  finally show  "f t= (a*(f 1 - f (a^2)) - (f (1/a^2) - f 1)/a)/(a + 1/a - (a^3 + 1/(a^3)))*t
        + ((f 1 - f (a^2))/a - a*(f (1/a^2) - f 1))/(a + 1/a - (a^3 + 1/(a^3)))/t"
    by simp
qed


definition C1 :: "(real\<Rightarrow>real) \<Rightarrow> real \<Rightarrow> real" where
"C1 f a = (a*(f 1 - f (a^2)) - (f (1/a^2) - f 1)/a)/(a + 1/a - (a^3 + 1/(a^3)))"


definition C2 :: "(real\<Rightarrow>real) \<Rightarrow> real \<Rightarrow> real" where
"C2 f a = ((f 1 - f (a^2))/a - a*(f (1/a^2) - f 1))/(a + 1/a - (a^3 + 1/(a^3)))"


theorem final_theorem:
  fixes t::real
  fixes a::real
  fixes f::"real\<Rightarrow>real"
  assumes "t > 0" "a > 1" "\<forall> x y. x > 0 \<and> y > 0 \<longrightarrow> (x + 1/x)*(f y) = f (x*y) + f (y/x)"
  shows "f t = (C1 f a)*t + (C2 f a)/t"
proof -

  have "f t= (a*(f 1 - f (a^2)) - (f (1/a^2) - f 1)/a)/(a + 1/a - (a^3 + 1/(a^3)))*t
          + ((f 1 - f (a^2))/a - a*(f (1/a^2) - f 1))/(a + 1/a - (a^3 + 1/(a^3)))/t"
    using assms lemma_divide_left by simp

  then show ?thesis
    using C1_def C2_def by presburger

qed


end
