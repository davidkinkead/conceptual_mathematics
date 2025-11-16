class HomomorphismSolver:
    def __init__(self):
        # Define the sets X and Y
        self.X = ['a', 'a1', 'a2', 'a3', 'a4', 'b', 'c', 'd', 'd1']
        self.Y = ['l', 'm', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']

        # Define alpha: X -> X
        self.alpha = {
            'a': 'a1',
            'a1': 'a2',
            'a2': 'a3',
            'a3': 'a4',
            'a4': 'a2',
            'b': 'a2',
            'c': 'a3',
            'd': 'd1',
            'd1': 'd'
        }

        # Define beta: Y -> Y
        self.beta = {
            'l': 'm', 'm': 'l',
            'p': 'r', 'q': 'r',
            'r': 't',
            's': 't',
            't': 'v',
            'u': 's',
            'v': 'u',
            'w': 'x', 'x': 'y', 'y': 'w',
            'z': 'y'
        }

        self.solutions = []

    def solve(self):
        """Starts the backtracking search for valid maps."""
        self.solutions = []
        # We pass an empty dictionary as the starting partial map
        self._backtrack(0, {})
        return self.solutions

    def _backtrack(self, x_idx, current_map):
        """
        Recursive function to find maps.
        x_idx: The index of the element in self.X we are currently trying to map.
        current_map: Dictionary representing the partial mapping f built so far.
        """
        
        # Base Case: If all elements in X are mapped, we have a complete solution.
        if x_idx == len(self.X):
            self.solutions.append(current_map.copy())
            return

        u = self.X[x_idx]

        # Optimization: If u is already mapped (due to propagation from a previous step),
        # we skip to the next element. The consistency was checked during propagation.
        if u in current_map:
            self._backtrack(x_idx + 1, current_map)
            return

        # Try mapping the current node u to every possible node v in Y
        for v in self.Y:
            # We will attempt to assign f(u) = v.
            # Because f(alpha(x)) must equal beta(f(x)), assigning f(u) = v
            # immediately forces specific values for f(alpha(u)), f(alpha(alpha(u))), etc.
            # We propagate these constraints forward.
            
            updates = {}
            valid_choice = True
            
            curr_x = u
            curr_y = v
            
            # Propagate the path from u
            while True:
                # Check for conflicts with existing map
                if curr_x in current_map:
                    if current_map[curr_x] != curr_y:
                        valid_choice = False # Conflict found
                    break # Path merges with previously mapped area
                
                # Check for conflicts within the current propagation chain (loops)
                if curr_x in updates:
                    if updates[curr_x] != curr_y:
                        valid_choice = False # Conflict within the new loop
                    break # Loop closed

                # Record the forced assignment
                updates[curr_x] = curr_y
                
                # Move to next step in the functional graphs
                curr_x = self.alpha[curr_x]
                curr_y = self.beta[curr_y]

            if valid_choice:
                # Apply updates to the map
                for k, val in updates.items():
                    current_map[k] = val
                
                # Recurse
                self._backtrack(x_idx + 1, current_map)
                
                # Backtrack: remove the updates to restore state for the next iteration
                for k in updates:
                    del current_map[k]

    def print_solutions(self):
        print(f"Found {len(self.solutions)} valid maps f: X -> Y.")
        print("-" * 40)
        
        # Sort solutions for consistent display (optional)
        # Sorting by the image tuple to make it deterministic
        self.solutions.sort(key=lambda m: tuple(m[k] for k in self.X))

        for i, sol in enumerate(self.solutions):
            print(f"Solution {i + 1}:")
            # Grouping output for readability based on components
            # Component 1: d, d1
            comp1 = f"f(d)={sol['d']}, f(d1)={sol['d1']}"
            
            # Component 2: Cycle
            cycle = f"f(a2)={sol['a2']}, f(a3)={sol['a3']}, f(a4)={sol['a4']}"
            
            # Component 2: Tails
            tails = f"f(a)={sol['a']}, f(a1)={sol['a1']}, f(b)={sol['b']}, f(c)={sol['c']}"
            
            print(f"  Comp 1: {comp1}")
            print(f"  Comp 2: {cycle}")
            print(f"  Tails : {tails}")
            print("-" * 20)

if __name__ == "__main__":
    solver = HomomorphismSolver()
    results = solver.solve()
    solver.print_solutions()
