from pysat.formula import WCNF
from pysat.card import CardEnc
import timeit
from pysat.card import CardEnc


def decode_sat_tuple(t_name):
    # Example: ('R', [0, 52]) -> T_R__0,52
    parts = t_name.split("__")
    table = parts[0][2:]   # remove "T_"
    values = parts[1].split(",")
    return {"table": table, "values": values}


class SATEncoder:

    def __init__(self):
        self.wcnf = WCNF()
        self.var_map = {}
        self.reverse_map = {}
        self.counter = 1

    def var(self, name):
        if name not in self.var_map:
            self.var_map[name] = self.counter
            self.reverse_map[self.counter] = name
            self.counter += 1
        return self.var_map[name]

    def add_clause(self, clause):
        self.wcnf.append(clause)

    def add_soft(self, clause, weight=1):
        self.wcnf.append(clause, weight=weight)

    def _add_dp_vs_constraints(self, witness_map, projection_map):
        """
        Standard Semantics: Kept = True, Deleted = False
        P <-> (W1 v W2...)  (Projection exists if any witness exists)
        W <-> (T1 ^ T2...)  (Witness exists if ALL its tuples exist)
        """
        # 1. Witness <-> All Tuples
        for w_name, tuples in witness_map.items():
            w_var = self.var(w_name)
            t_vars = [self.var(t) for t in tuples]
            # W -> T (If witness kept, all tuples must be kept)
            for t_var in t_vars:
                self.add_clause([-w_var, t_var])
            # T1 ^ T2... -> W (If all tuples kept, witness is kept)
            self.add_clause([w_var] + [-t_var for t_var in t_vars])

        # 2. Projection <-> Any Witness
        for p_name, witnesses in projection_map.items():
            p_var = self.var(p_name)
            w_vars = [self.var(w) for w in witnesses]
            # P -> (W1 v W2...) (If projection kept, at least one witness must be kept)
            self.add_clause([-p_var] + w_vars)
            # W -> P (If any witness kept, projection is kept)
            for w_var in w_vars:
                self.add_clause([-w_var, p_var])

    def _add_swp_constraints(self, witness_map, projection_map):

        for proj, witnesses in projection_map.items():
            p_var = self.var(proj)
            w_vars = [self.var(w) for w in witnesses]

            # Projection → witnesses
            self.add_clause([-p_var] + w_vars)

            # Force projection alive
            self.add_clause([p_var])

        for w, tuples in witness_map.items():
            w_var = self.var(w)

            for t in tuples:
                t_var = self.var(f"T_{t}")

                self.add_clause([-w_var, t_var])

    def _add_dp_ss_constraints(self, witness_map, projection_map):
        for w_name, tuples in witness_map.items():
            w_var = self.var(w_name)

            # W → T
            for t_name in tuples:
                self.add_clause([-w_var, self.var(t_name)])

            # T → W  (add this)
            clause = [w_var]
            for t_name in tuples:
                clause.append(-self.var(t_name))
            self.add_clause(clause)
    # Placeholder for _add_resilience_constraints
    def _add_resilience_constraints(self, witness_map):
        raise NotImplementedError("'_add_resilience_constraints' is not implemented yet.")

    # Placeholder for _add_adp_ss_constraints
    def _add_adp_ss_constraints(self, witness_map, projection_map):
        raise NotImplementedError("'_add_adp_ss_constraints' is not implemented yet.")

    def add_dependency_constraints(
        self,
        witness_map,
        projection_map,
        mode="dp_ss"
      ):

        print(f"\n[Encoder] Adding constraints for mode: {mode}")

        if mode == "dp_ss":
            self._add_dp_ss_constraints(witness_map, projection_map)

        elif mode == "dp_vs":
            self._add_dp_vs_constraints(witness_map, projection_map)

        elif mode == "swp":
            self._add_swp_constraints(witness_map, projection_map)

        elif mode == "resilience":
            self._add_resilience_constraints(witness_map)

        elif mode == "adp_ss":
            self._add_adp_ss_constraints(witness_map, projection_map)

        else:
            raise ValueError(f"Unknown mode: {mode}")

        print("[Encoder] Constraints added successfully")

    # ================================
    # ADP-SS OBJECTIVE (FIXED)
    # ================================
     # Placeholder for _add_adp_ss_constraints
    def _add_adp_ss_constraints(self, witness_map, projection_map):
        """
        Standard Logic Wiring: Kept=True, Deleted=False
        P <=> (W1 v W2...)
        W <=> (T1 ^ T2...)
        """
        # 1. Witness <-> Tuples (W is alive ONLY IF all its T are alive)
        for w_name, tuples in witness_map.items():
            w_var = self.var(w_name)
            t_vars = [self.var(t) for t in tuples]

            # W -> T_i (If witness exists, every tuple must exist)
            for t_var in t_vars:
                self.add_clause([-w_var, t_var])

            # (T1 ^ T2...) -> W (If all tuples exist, witness exists)
            self.add_clause([w_var] + [-t_var for t_var in t_vars])

        # 2. Projection <-> Witnesses (P is alive ONLY IF at least one W is alive)
        for p_name, witnesses in projection_map.items():
            p_var = self.var(p_name)
            w_vars = [self.var(w) for w in witnesses]

            # P -> (W1 v W2...) (If projection survives, it needs a witness)
            self.add_clause([-p_var] + w_vars)

            # W_i -> P (If any witness survives, the projection survives)
            for w_var in w_vars:
                self.add_clause([-w_var, p_var])

    def set_adp_ss_objective(self, all_projections_list, b, w_tuple=1):
        # Map projection names to their SAT variables
        projection_literals = [self.var(proj) for proj in all_projections_list]
        total_p = len(projection_literals)

        # --- Constraint 1: Kill at least 'b' (Keep at most Total - b) ---
        max_to_keep = total_p - b
        if max_to_keep < 0: max_to_keep = 0

        print(f"[ADP-SS] Total: {total_p} | Kill Goal: >= {b} (Keep <= {max_to_keep})")

        card_atmost = CardEnc.atmost(
            lits=projection_literals,
            bound=max_to_keep,
            top_id=self.counter,
            encoding=1
        )
        for clause in card_atmost.clauses:
            self.add_clause(clause)
        self.counter = max(self.counter, card_atmost.nv)

        # --- Constraint 2: Safety Valve (Keep at least 1 projection alive) ---
        # This ensures we don't kill the entire view.
        card_atleast = CardEnc.atleast(
            lits=projection_literals,
            bound=1,
            top_id=self.counter,
            encoding=1
        )
        for clause in card_atleast.clauses:
            self.add_clause(clause)
        self.counter = max(self.counter, card_atleast.nv)

        # --- Constraint 3: Minimize Tuple Deletions ---
        # We want to keep tuples alive (True), so we add soft clauses for [T_var]
        for name, var_id in self.var_map.items():
            if name.startswith("T_"):
                # A soft clause [ID] encourages the solver to keep the tuple TRUE.
                self.add_soft([var_id], weight=w_tuple)

        print("[ADP-SS] Surgical objective complete.")

        # Placeholder for _enforce_non_target_projections_true
    def _enforce_non_target_projections_true(self, projection_map, target_proj):
        raise NotImplementedError("'_enforce_non_target_projections_true' is not implemented yet.")

    def set_dp_ss_objective(self, target_proj, projection_map, w_tuple=1):
        """
        1. HARD: All witnesses of target must be FALSE (Deleted).
        2. SOFT: All tuples should be TRUE (Minimize deletions).
        """
        # Kill every witness that could produce the target
        target_witnesses = projection_map.get(target_proj, [])
        for w_name in target_witnesses:
            self.add_clause([-self.var(w_name)])

        # Minimize tuple deletions
        for name, var_id in self.var_map.items():
            if name.startswith("T_"):
                # Penalize the solver for making a tuple FALSE
                self.add_soft([var_id], weight=w_tuple)
    def set_dp_vs_objective(self, target_proj, all_projections, w_projection=1):
        """
        Goal: Delete target, minimize other projection deletions, minimize tuple deletions.
        """
        # HARD: Target projection must be FALSE (Deleted)
        self.add_clause([-self.var(target_proj)])

        # SOFT: Keep other projections TRUE (Weight: w_projection)
        for proj in all_projections:
            if proj != target_proj:
                self.add_soft([self.var(proj)], weight=w_projection)

        # SOFT: Keep tuples TRUE (Weight: 1)
        # This ensures we don't delete extra tuples for no reason
        for name, var_id in self.var_map.items():
            if name.startswith("T_"):
                self.add_soft([var_id], weight=1)

    def set_swp_objective(self, projection_map, witness_map):
        """
        SWP Objective:

        Minimize number of kept base tuples
        (Optional: also minimize witnesses for tighter solutions)
        """

        # -------------------------
        # Collect all tuples
        # -------------------------
        all_tuples = set()
        for tuples in witness_map.values():
            all_tuples.update(tuples)

        # -------------------------
        # SOFT: minimize tuples
        # -------------------------
        for t in all_tuples:
            t_var = self.var(f"T_{t}")

            # Prefer tuple to be deleted
            self.add_soft([-t_var], weight=10)

        # -------------------------
        # OPTIONAL: minimize witnesses
        # -------------------------
        for w in witness_map:
            w_var = self.var(w)

            self.add_soft([-w_var], weight=1)

    def set_resilience_objective(self, witness_map, w_tuple=1):
      """
      RESILIENCE Objective:

      Goal:
          Minimize number of tuple deletions such that ALL witnesses are FALSE.

      Encoding:
          HARD: kill all witnesses
          SOFT: minimize tuple deletions
      """

      # -------------------------
      # HARD: kill ALL witnesses
      # -------------------------
      for w_name in witness_map:
          self.add_clause([-self.var(w_name)])

      # -------------------------
      # SOFT: minimize deletions
      # -------------------------
      for name, var in self.var_map.items():
          if name.startswith("T_"):
              self.add_soft([var], weight=w_tuple)

    # ================================
    # Utility functions
    # ================================
    def decode_sat_tuple(self, t_name, cast_int=False):

        if not t_name.startswith("T_"):
            raise ValueError(f"Invalid tuple name: {t_name}")

        table, values_str = t_name[2:].split("__", 1)

        values = []
        if values_str:
            for v in values_str.split(","):
                v = int(v) if cast_int and v.isdigit() else v
                values.append(v)

        return {"table": table, "values": values}

    def pretty_tuple(self, t_name):
        t = self.decode_sat_tuple(t_name)
        return f"{t['table']}({', '.join(map(str, t['values']))})"

    def check_encode_decode_consistency(self, tuple_names):

          errors = []

          for t_name in tuple_names:

              try:
                  decoded = self.decode_sat_tuple(t_name)
                  re_encoded = encode_sat_tuple(
                      decoded['table'],
                      decoded['values']
                  )

                  if t_name != re_encoded:
                      errors.append((t_name, re_encoded))

              except Exception as e:
                  errors.append((t_name, str(e)))

          # -------------------------
          # Report
          # -------------------------
          if not errors:
              print("\u2705 All tuples are encode-decode consistent")
          else:
              print("\u274C Inconsistencies found:")
              for orig, new in errors:
                  print(f"  {orig}  \u2192  {new}")

          return errors
