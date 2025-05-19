
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct InternedSets {
    sets: Vec<Vec<usize>>,
    set_backmap: HashMap<Vec<usize>, usize>,
    best_utility_seen: Vec<usize>,
}

// fn new_interned_sets() -> InternedSets {
//     InternedSets {
//         sets: Vec::new(),
//         set_backmap: HashMap::new(),
//         best_utility_seen: Vec::new(),
//     }
// }

impl InternedSets {
    pub fn new() -> Self {
        InternedSets {
            sets: Vec::new(),
            set_backmap: HashMap::new(),
            best_utility_seen: Vec::new(),
        }
    }

    pub fn get_utility(&self, index: usize) -> usize {
        self.best_utility_seen[index]
    }

    pub fn intern(&mut self, set: &Vec<usize>, utility: usize) -> usize {
        if let Some(&index) = self.set_backmap.get(set) {
            if utility > self.best_utility_seen[index] {
                self.best_utility_seen[index] = utility;
            }
            return index;
        }
        self.sets.push(set.clone());
        let index = self.sets.len() - 1;
        self.set_backmap.insert(set.clone(), index);
        self.best_utility_seen.push(utility);
        return index;
    }

    pub fn len(&self) -> usize {
        self.sets.len()
    }

}