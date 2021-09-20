theory mi18472_Aleksandra_Radosavljevic
  imports Complex_Main
begin

text \<open>
  a b c d su realni brojevi takvi da vazi "a + b +c + d = 6"
   i "a^2 + b^2 +c^2 + d^2 =12"
 dokazati da vazi nejednakost 
 36 \<le> 4*(a^3 + b^3 +c^3 + d^3)-(a^4 + b^4 +c^4 + d^4)\<le> 48
\<close>



lemma konacna:
  fixes a b c d :: real
  assumes "a + b + c + d = 6"
  assumes "a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 = 12"
  shows "36 \<le> 4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4)"
        and "4 * (a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) \<le> 48"
  sorry
end
