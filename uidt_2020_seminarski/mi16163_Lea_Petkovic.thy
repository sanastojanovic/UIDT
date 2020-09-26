theory seminarski 
  imports Main
begin

(* 
   Student: Lea Petkovic 163/2016
   Seminarski rad iz UIDT-a
*)

text\<open>
  https://imomath.com/srb/zadaci/2016_opstinsko.pdf
  Strana 5, prvi zadatak, prvi razred
  
  Neka su dati skupovi A, B i C. Koja od inkluzija mora vaziti za skupove
\<close>

(* Resenje zadatka:
(A \ (B \ C)) \ (B \ (C \ A)) = (A \ (B \<inter> -C)) \ (B \ (C \<inter> -A))      I se oslobadjamo razlike         
      = (A \<inter> -(B \<inter> -C)) \ (B \<inter> -(C \<inter> -A))                
      = (A \<inter> -(B \<inter> -C)) \<inter> -(B \<inter> -(C \<inter> -A))               
      = (A \<inter> (-B \<union> C)) \<inter> (-B \<union> (C \<inter> -A))                 
      = (A \<inter> (-B \<union> C) \<inter> -B) \<union> (A \<inter> (-B \<union> C) \<inter> C \<inter> -A)    
      = (A \<inter> -B) \<union> (\<emptyset> \<inter> (-B \<union> C) \<inter> C)                     
      = (A \<inter> -B) \<union> \<emptyset>
      = A \<inter> -B = A \ B.
Dakle, posto vazi B \<inter> C \<subseteq> B, dobijamo A \ (B \<inter> C) \<supseteq> A \ B,
tj.  A \ (B \<inter> C) \<supseteq> (A \ (B \ C)) \ (B \ (C \ A))   *)

lemma pomocna_lema:
  shows "B \<inter> C \<subseteq> B"
proof
  fix x
  assume "x \<in> B \<inter> C"
  then have "x \<in> B" "x \<in> C"
    by auto
  then show "x \<in> B"
    by auto
qed


lemma zadatak:
  shows "(A - (B - C)) - (B - (C - A)) \<subseteq> A - (B \<inter> C) "
proof
  fix x
  assume "x \<in> (A - (B - C)) - (B - (C - A))"
  then have "x \<in> (A - (B \<inter> -C)) - (B - (C \<inter> -A))"                       (*using prva_jednakost *)
    by auto
  then have "x \<in> (A \<inter> (-(B \<inter> -C))) - (B \<inter> (-(C \<inter> -A)))"                 
    by auto
  then have "x \<in> (A \<inter> (-(B \<inter> -C))) \<inter> ( -(B \<inter> (-(C \<inter> -A))) )"            
    by auto
  then have "x \<in> (A \<inter> (-B \<union> C)) \<inter> (-B \<union> (C \<inter> -A))"                      (*using druga_jednakost*)
    by auto
  then have "x \<in> (A \<inter> (-B \<union> C) \<inter> (-B)) \<union> (A \<inter> (-B \<union> C) \<inter> (C \<inter> -A))"    (*using treca_jednakost*)
    by auto
  then have "x \<in> (A \<inter> -B) \<union> ({}  \<inter> (-B \<union> C) \<inter> C)"         
    by auto
  then have "x \<in> (A \<inter> -B) \<union> {}"                                         
    by auto
  then have "x \<in> A \<inter> -B"
    by auto
  then show "x \<in> A - B \<inter> C"
    using pomocna_lema
    by auto
qed

(* Pojedinacno dokazane koje se koriste *)
lemma prva_jednakost:
  shows "A - B = A \<inter> -B"
proof
  show "A - B \<subseteq> A \<inter> -B"
  proof
    fix x
    assume "x \<in> A - B"
    then have "x \<in> A" "x \<notin> B"
      by auto
    then have "x \<in> -B"
      by auto
    then show "x \<in> A \<inter> -B"
      using \<open>x \<in> A\<close> \<open>x \<in> -B\<close>
      by blast
  qed
next
  show "A \<inter> -B \<subseteq> A - B"
  proof
    fix x
    assume "x \<in> A \<inter> -B"
    then have "x \<in> A" "x \<in> -B"
      by auto
    then have "x \<notin> B"
      by auto
    then show "x \<in> A - B"
      using \<open>x \<in> A\<close> \<open>x \<notin> B\<close>
      by auto
  qed
qed

lemma druga_jednakost:
  shows "-(B \<inter> C) = -B \<union> -C"
proof
  show "-(B \<inter> C) \<subseteq> -B \<union> -C"
    by auto
next
  show "-B \<union> -C \<subseteq> -(B \<inter> C)"
  proof
    fix x
    assume "x \<in> -B \<union> -C"
    then have "x \<in> -B \<or> x \<in> -C"
      by auto
    then show "x \<in> -(B \<inter> C)"
    proof
      assume "x \<in> -B"
      then have "x \<notin> B"
        by auto
      then have "x \<notin> B \<inter> C"
        by auto
      then show "x \<in> - (B \<inter> C)"
        by auto
    next
      assume "x \<in> -C"
      then have "x \<notin> C"
        by auto
      then have "x \<notin> B \<inter> C"
        by auto
      then show "x \<in> - (B \<inter> C)"
        by auto
    qed
  qed
qed

lemma treca_jednakost:
  shows "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  (* by (simp add: Int_Un_distrib) *)
proof
  show "A \<inter> (B \<union> C) \<subseteq> A \<inter> B \<union> A \<inter> C"
  proof
    fix x
    assume "x \<in> A \<inter> (B \<union> C)"
    then have "x \<in> A" "x \<in> B \<or> x \<in> C"
      by auto
    then have "x \<in> A \<and> x \<in> B \<or> x \<in> A \<and> x \<in> C"
      by auto
    then have "x \<in> A \<inter> B \<or> x \<in> A \<inter> C"
      by auto
    then show "x \<in> (A \<inter> B) \<union> (A \<inter> C)"
      by auto
  qed
next
  show "(A \<inter> B) \<union> (A \<inter> C) \<subseteq> A \<inter> (B \<union> C)"
  proof
    fix x
    assume "x \<in> (A \<inter> B) \<union> (A \<inter> C)"
    then have "x \<in> A \<inter> B \<or> x \<in> A \<inter> C"
      by auto
    then have "(x \<in> A \<and> x \<in> B) \<or> (x \<in> A \<and> x \<in> C)"
      by auto
    then have "x \<in> A" "x \<in> B \<or> x \<in> C"
      by auto
    then show "x \<in> A \<inter> (B \<union> C)"
      by auto
  qed
qed


end
