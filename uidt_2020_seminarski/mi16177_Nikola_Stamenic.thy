theory mi16177_Nikola_Stamenic
  imports Main
begin

text\<open>
  https://imomath.com/srb/zadaci/2020_opstinsko.pdf
  Prvi razred - B kategorija, zadatak 4.

  Dokazati da za ma koje skupove A, B, C i D vazi jednakost

  (A \<union> B)\(C \<inter> D)\(A \<union> C)\(B \<inter> D) = (B \ C)\(A \ D)

\<close>

lemma "(((A \<union> B)-(C \<inter> D))-((A \<union> C)-(B \<inter> D) )) = (B-C)-(A-D)"
  by auto


lemma "(((A \<union> B)-(C \<inter> D))-((A \<union> C)-(B \<inter> D) )) = (B-C)-(A-D)" (is "?l=?d")
proof
  show "?l \<subseteq> ?d"
  proof
    fix x
    assume "x \<in> ?l"
  then have "x \<in> A \<union> B - C \<inter> D" "x \<notin> A \<union> C - B \<inter> D"
      by auto
    then have "x \<in> A \<union> B" "x \<notin> C \<inter> D"
      by auto 
    then have "x \<in> A \<or> x \<in> B"
      by auto
    then have "x \<notin> C \<or> x \<notin> D"
      using \<open>x \<notin> C \<inter> D\<close> by auto
    (*Trebace nam kasnije da ne pripada oba skupa*)
    from \<open>x \<notin> A \<union> C - B \<inter> D\<close> 
    have "x \<notin> A \<union> C \<or> x \<in> A \<union> C \<and> x \<in> B \<inter> D"
      by auto
    (*Delimo na dva slucaja, u zavisnosti kako je formirana razlika.
      Da li pripada oba skupa ili ne pripada prvom 
     (u ovom slucaju nije bitna pripadnost drugom skupu)*)
    then show "x \<in> ?d"
    proof
    (*x \<in> A \<union> B - C \<inter> D \<and> x \<notin> A \<union> C*)
      assume "x \<notin> A \<union> C"
      then have "x\<notin> A" "x \<notin> C"
        by auto
      then have "x \<in> B"
        using \<open>x \<in> A \<or> x \<in> B\<close> by auto
       (*Kako pripada A \<union> B i ne pripada A, onda pripada B 
       ( sto nam i treba za desnu stranu)*)
      then have "x \<notin> A - D"
        using \<open>x \<notin> A\<close> by auto
      (*Kako ne pripada A, ne moze pripadati ni A - D*)
      then have "x \<in> B - C"
        using \<open>x \<in> B\<close> \<open>x \<notin> C\<close>
        by auto
      (*Dokazano*)
      then show "x \<in> ?d" using \<open>x \<notin> A - D\<close> by auto
    next
      (*x \<in> A \<union> B - C \<inter> D \<and> x \<in> A \<union> C \<and> x \<in> B \<inter> D*)
      assume "x \<in> A \<union> C \<and> x \<in> B \<inter> D"
      then have "x \<in> B" "x \<in> D"
        by auto
      (*Pripada preseku, samim tim i oba skupa, 
        sto nam je bitno zbog B-C da pripada B,
        ili ako x \<in> A, onda mora pripadati i D
        zbog A - D*)
      then have "x \<notin> C"
        using \<open>x \<notin> C \<or> x \<notin> D\<close> by auto
      (*x \<notin> C \<inter> D, a pripada D, onda mora x \<notin> C,
        sto nam odgovara zbog B - C*)
      then have "x \<in> A"
        using \<open>x \<in> A \<union> C \<and> x \<in> B \<inter> D\<close> by auto
      then have "x \<in> B - C" 
        using \<open>x \<in> B\<close> \<open>x \<notin> C\<close> by auto
      (*Leva strana razlike u desnoj strani jednakosti dokazana*)
      then have "x \<notin> A - D"
        using \<open>x \<in> A\<close> \<open>x \<in> D\<close> by auto
      (*Desna strana razlike u desnoj strani jednakosti dokazana*)
      then show "x \<in> ?d"
        using \<open>x \<in> B - C\<close> \<open>x \<notin> A - D\<close> by auto
      (*Dokazano ?l \<subseteq> ?d*)
    qed
  qed
next 
  show "?d \<subseteq> ?l"
  proof
    fix x 
    assume "x \<in> ?d"
    then have "x \<in> B-C" "x \<notin> A-D"
      by auto
    then have "x \<in> B" "x \<notin> C" "x \<notin> A \<or> x \<in> A \<and> x \<in> D" 
      by auto
    then have "x \<notin> A \<or> x \<in> A \<and> x \<in> D"
      by auto
    then show "x \<in> ?l"
    proof
      assume "x \<notin> A"
      (*x \<in> (A \<union> B) - (C \<inter> D) *)
      then have "x \<in> A \<union> B" 
        using \<open>x \<in> B\<close> by auto
      then have "x \<notin> C \<inter> D"
        using \<open>x \<notin> C\<close> by auto
      then have "x \<in> (A \<union> B) - (C \<inter> D)"
        using \<open>x \<in> A \<union> B\<close> by auto
        (*Dokazano*)

        (*x \<notin> (A \<union> C) - (B \<inter> D) *)
      then have "x \<notin> A \<union> C"
        using \<open>x \<notin> A\<close> \<open>x \<notin> C\<close> by auto
      then have "x \<notin> (A \<union> C) - (B \<inter> D)"
        by auto
      (*Dokazano*)

      (*x \<in> ?l*)
      then show "x \<in> ?l"
        using \<open>x \<in>(A \<union> B) - (C \<inter> D)\<close> by auto
    next
      assume "x \<in> A \<and> x \<in> D"
      then have "x \<in> A" "x \<in> D"
        by auto
      (*x \<in> (A \<union> B) - (C \<inter> D) *)
      then have "x \<in> A \<union> B" "x \<in> A \<union> C"
        by auto
      then have "x \<notin> C \<inter> D"
        using \<open>x \<notin> C\<close> by auto
      then have "x \<in> (A \<union> B) - (C \<inter> D)"
        using \<open>x \<in> A \<union> B\<close> by auto
        (*Dokazano*)

        (*x \<notin> (A \<union> C) - (B \<inter> D) *)
      then have "x \<in> B \<inter> D"
        using \<open>x \<in> B\<close> \<open>x \<in> D\<close> by auto
      then have "x \<notin> (A \<union> C) - (B \<inter> D)"
        (*Dokazano*)

        (*x \<in> ?l *)
        using \<open>x \<in> A \<union> C\<close> by auto
      then show "x \<in> ?l"
        using \<open>x \<in>(A \<union> B) - (C \<inter> D)\<close> by auto
    qed
  qed
qed


end