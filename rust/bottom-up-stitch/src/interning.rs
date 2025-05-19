
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct InternedSets {
    parents_left: Vec<i32>,
    parents_right: Vec<i32>,
    sets: Vec<Vec<usize>>,
    parent_set_left: Vec<i32>,
    parent_set_right: Vec<i32>,
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
    pub fn new(parents_left: Vec<i32>, parents_right: Vec<i32>) -> InternedSets {
        InternedSets {
            parents_left: parents_left,
            parents_right: parents_right,
            sets: Vec::new(),
            parent_set_left: Vec::new(),
            parent_set_right: Vec::new(),
            set_backmap: HashMap::new(),
            best_utility_seen: Vec::new(),
        }
    }

    pub fn get_utility_for_set(&self, value: &Vec<usize>) -> usize {
        if let Some(&index) = self.set_backmap.get(value) {
            return self.best_utility_seen[index];
        }
        return 0
    }

    pub fn intern(&mut self, set: &Vec<usize>, utility: usize) -> usize {
        if let Some(&index) = self.set_backmap.get(set) {
            if utility > self.best_utility_seen[index] {
                self.best_utility_seen[index] = utility;
            }
            return index;
        }
        let parent_set_left = set.iter()
            .map(|&x| self.parents_left[x])
            .filter(|&x| x != -1)
            .map(|x| x as usize)
            .collect::<Vec<usize>>();
        let parent_set_left_idx: i32 = if parent_set_left.len() < 2 { -1 } else { self.intern(&parent_set_left, utility) as i32 };
        let parent_set_right = set.iter()
            .map(|&x| self.parents_right[x])
            .filter(|&x| x != -1)
            .map(|x| x as usize)
            .collect::<Vec<usize>>();
        let parent_set_right_idx: i32 = if parent_set_right.len() < 2 { -1 } else { self.intern(&parent_set_right, utility) as i32 };
        self.parent_set_left.push(parent_set_left_idx);
        self.parent_set_right.push(parent_set_right_idx);
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