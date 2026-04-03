theory ProstorVerovatnoce
  imports Main
begin

definition sigma_algebra :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "sigma_algebra \<Omega> F \<longleftrightarrow>
        (\<forall>A \<in> F . A \<subseteq> \<Omega>) \<and>
        (\<Omega> \<in> F) \<and>
        (\<forall>A \<in> F . \<Omega>-A \<in> F) \<and>
        (\<forall>A :: nat \<Rightarrow> 'a set . (\<forall>n . A n \<in> F) \<longrightarrow> (\<Union> n . A n ) \<in> F)
"

lemma 
  assumes "sigma_algebra \<Omega> F"
  shows "{} \<in> F"
proof -
  have "\<Omega> \<in> F"
    using assms unfolding sigma_algebra_def
    by auto
  moreover have "\<Omega>-\<Omega> \<in> F"
    using assms unfolding sigma_algebra_def
    by auto
  ultimately show "{} \<in> F"
    by auto
qed

lemma 
  assumes "sigma_algebra \<Omega> F"
  shows "(\<forall>A :: nat \<Rightarrow> 'a set . (\<forall>n . A n \<in> F) \<longrightarrow> (\<Inter>n . A n ) \<in> F)"
(*proof 
  fix A :: "nat \<Rightarrow> 'a set"
  show "(\<forall>n . A n \<in> F) \<longrightarrow> (\<Inter>n . A n ) \<in> F"
  proof
    assume "\<forall>n . A n \<in> F"
    have "\<forall>n . (\<Omega> - A n) \<in> F"
      using assms \<open>\<forall>n . A n \<in> F\<close> unfolding sigma_algebra_def
      by auto
    then have "(\<Union>n . \<Omega> - A n) \<in> F"
      using assms unfolding sigma_algebra_def
      by auto
    then have "\<Omega> - (\<Union>n . \<Omega> - A n) \<in> F"
      using assms unfolding sigma_algebra_def
      by auto
    moreover have "\<Omega> - (\<Union>n . \<Omega> - A n) = (\<Inter>n . A n)"
      by auto
    ultimately show "(\<Inter>n . A n ) \<in> F"
      by auto
  qed *)
  sorry

lemma 
  assumes "sigma_algebra \<Omega> F"
  shows "\<forall>A \<in> F . \<forall> B \<in> F . A \<union> B \<in> F"
  sorry

lemma 
  assumes "sigma_algebra \<Omega> F"
  shows "\<forall>A \<in> F . \<forall> B \<in> F . A \<inter> B \<in> F"
  sorry



end