Theory spec_arm8
Ancestors words arm8

(* ----------------- *)
(* Utility functions *)
(* ----------------- *)

Definition arm8_load_64_def:
  arm8_load_64 m a =
  (((m (a + 7w)) @@
  (((m (a + 6w)) @@
  (((m (a + 5w)) @@
  (((m (a + 4w)) @@
  (((m (a + 3w)) @@
   (((m (a + 2w)) @@
     ((m (a + 1w)) @@ (m (a + 0w))):bool[16]):bool[24])):bool[32])
    ):bool[40])):bool[48])):bool[56])):bool[64])
End