import Logic.Propositional

-- [a => b, b => c] |- a => c
problem1_1 :: Proof
problem1_1 =
  ImpliesIntro (a ~> c)
  (ImpliesElim c
   (ImpliesElim b
    (Assumption a)
    (Assumption (a ~> b)))
   (Assumption (b ~> c)))

-- ((a | b) => c) => ((a => c) & (b => c))
problem1_2 :: Proof
problem1_2 =
  ImpliesIntro (((a ~| b) ~> c) ~> ((a ~> c) ~& (b ~> c)))
  -- assume (a ~| b) ~> c
  (AndIntro ((a ~> c) ~& (b ~> c))
   (ImpliesIntro (a ~> c)
    -- assume a, (a ~| b) ~> c
    (ImpliesElim c
     (OrIntroL (a ~| b)
      (Assumption a))
     (Assumption ((a ~| b) ~> c))))
   (ImpliesIntro (b ~> c)
    -- assume b, (a ~| b) ~> c
    (ImpliesElim c
     (OrIntroR (a ~| b)
      (Assumption b))
     (Assumption ((a ~| b) ~> c)))))

-- (a => (b => c)) => ((a & b) => c)
problem1_3 :: Proof
problem1_3 =
  ImpliesIntro ((a ~> (b ~> c)) ~> ((a ~& b) ~> c))
  -- assume a ~> (b ~> c)
  (ImpliesIntro ((a ~& b) ~> c)
   -- assume a ~& b
   (ImpliesElim c
    (AndElimR b
     (Assumption (a ~& b)))
    (ImpliesElim (b ~> c)
     (AndElimL a
      (Assumption (a ~& b)))
     (Assumption (a ~> (b ~> c))))))

-- (a => b) => (!b => !a)
problem1_4_a :: Proof
problem1_4_a =
  ImpliesIntro ((a ~> b) ~> (neg b ~> neg a))
  -- assume a ~> b
  (ImpliesIntro (neg b ~> neg a)
   -- assume neg b
   (ImpliesIntro (neg a)
    -- assume a
    (ImpliesElim bot
     (ImpliesElim b
      (Assumption a)
      (Assumption (a ~> b)))
     (Assumption (neg b)))))

-- a => !!a
problem1_4_b :: Proof
problem1_4_b =
  ImpliesIntro (a ~> neg (neg a))
  -- assume a
  (ImpliesIntro (neg (neg a))
   -- assume neg a
   (ImpliesElim bot
    (Assumption a)
    (Assumption (neg a))))

-- [a | b] |- !(!a & !b)
problem1_5 :: Proof
problem1_5 =
  -- assume a ~| b
  (OrElim (neg (neg a ~& neg b))
   (Assumption (a ~| b))
   -- assume a
   (ImpliesIntro (neg (neg a ~& neg b))
    -- assume (neg a ~& neg b)
    (ImpliesElim bot
     (Assumption a)
     (AndElimL (neg a)
      (Assumption (neg a ~& neg b)))))
   -- assume b
   (ImpliesIntro (neg (neg a ~& neg b))
    -- assume (neg a ~& neg b)
    (ImpliesElim bot
     (Assumption b)
      (AndElimR (neg b)
       (Assumption (neg a ~& neg b))))))
