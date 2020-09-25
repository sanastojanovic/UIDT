theory mi19435_Viseslav_Djuric
  imports Main
begin
text \<open>
Link ka zadatku: https://imomath.com/srb/zadaci/2014_okruzno.pdf
Prvi razrad, B kategorija, Zadatak 1:
  Za skupove A, B, C, neka je

P = (A \ B) \<union> C i Q = (A \<union> C) \ B.
Ispitati da li za sve ovakve skupove vai neka od relacija
P \<subseteq> Q, P = Q ili Q \<subseteq> P
\<close>

(* Postupak:
(A\B)\<union>C = (A\<inter>-B)\<union>C

(A\<union>C)\B = (A\<union>C) \<inter> -B =
= (A\<inter>-B) \<union> (C\<inter>-B) = 
= (A\B) \<union> (C\B) 

\<Rightarrow> (A\<union>C)\B \<subseteq> (A\B)\<union>C jer C\B \<subseteq> C jer C\B = C\<inter>-B jer C\<inter>-B\<subseteq>C 
*)

lemma pomocnaA:
  shows "A-B =A\<inter>-B"
proof
  show "A-B \<subseteq> A\<inter>-B"
  proof
    fix x
    assume "x\<in>A-B"
    then have "x\<in>A" "x\<notin>B"
      by auto
    then have "x\<in>-B"
      by auto
    then show "x\<in>A\<inter>-B"
      using `x\<in>A` `x\<in>-B`
      by auto
  qed
next
  show "A\<inter>-B \<subseteq> A-B"
  proof
    fix x
    assume "x\<in>A\<inter>-B"
    then have "x\<in>A" "x\<in>-B"
      by auto
    then have "x\<notin>B"
      by auto
    then show "x\<in>A-B"
      using `x\<in>A` `x\<notin>B`
      by auto
  qed
qed


lemma pomocnaC:
  shows "C-B = C\<inter>-B"
proof
  show "C-B \<subseteq> C\<inter>-B"
  proof
    fix x
    assume "x\<in>C-B"
    then have "x\<in>C" "x\<notin>B"
      by auto
    then have "x\<in>-B"
      by auto
    then show "x\<in>C\<inter>-B"
      using `x\<in>C` `x\<in>-B`
      by auto
  qed
next
  show "C\<inter>-B \<subseteq> C-B"
  proof
    fix x
    assume "x\<in>C\<inter>-B"
    then have "x\<in>C" "x\<in>-B"
      by auto
    then have "x\<notin>B"
      by auto
    then show "x\<in>C-B"
      using `x\<in>C` `x\<notin>B`
      by auto
  qed
qed

lemma pomocna:
shows "C-B \<subseteq>C"
  using pomocnaC
  by auto

lemma glavni_deo:
  shows "(A\<union>C)-B \<subseteq> (A-B)\<union>C"
(is "?levo \<subseteq> ?desno")
proof
  fix x
  assume "x\<in>(A\<union>C)-B"
  from this have "x\<in>(A\<union>C)\<inter>-B"
    by auto
  from this have "x\<in>(A\<inter>-B) \<union> (C\<inter>-B)"
    by auto
  from this have "x\<in>(A-B) \<union> (C-B)"
    using pomocnaC (* ili pomocnaA *)
    by auto
  from this have "x\<in>(A-B) \<or> x\<in>(C-B)"
    by auto
  from this show "x\<in>?desno"
  proof
    assume "x\<in>A-B"
    from this show "x\<in>?desno"
      by auto
  next
    assume "x\<in>C-B"
    from this show "x\<in>?desno"
      using pomocna
      by auto
  qed
qed


end
