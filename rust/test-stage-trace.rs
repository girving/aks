#!/usr/bin/env -S cargo +nightly -Zscript
//! Trace exactly what separatorStage does at each stage.
//! Shows the chunk structure and compares with Seiferas's design.

fn main() {
    let n = 16usize;
    let max_level = (n as f64).log2() as usize; // 4

    println!("n = {}, maxLevel = {}\n", n, max_level);

    println!("=== What separatorStage does (current Lean code) ===\n");
    println!("separatorSortingNetwork concatenates stages 0, 1, ..., numStages-1.");
    println!("Each stage t calls separatorStage(n, sep, t).\n");

    for t in 0..8 {
        let chunk_size = n / (1 << t); // n / 2^t (integer division)
        let num_chunks = 1 << t;       // 2^t
        print!("Stage {}: chunkSize={}, numChunks={}", t, chunk_size, num_chunks);
        if chunk_size <= 1 {
            println!(" → NO-OP (chunk ≤ 1)");
        } else {
            print!(" → apply separator to: ");
            let mut chunks = Vec::new();
            for k in 0..num_chunks {
                let offset = k * chunk_size;
                if offset + chunk_size <= n {
                    chunks.push(format!("[{},{})", offset, offset + chunk_size));
                }
            }
            println!("{}", chunks.join(", "));
        }
    }

    println!("\nWith numStages = 10 (as in seiferas_implies_sorting_network):");
    println!("  Stages 0-3: apply separator at levels 0-3 (chunk sizes 16,8,4,2)");
    println!("  Stage 4: chunkSize = 16/16 = 1 → NO-OP");
    println!("  Stages 5-9: chunkSize = 0 → NO-OP");
    println!("  TOTAL USEFUL STAGES: {} (= maxLevel)", max_level);

    println!("\n=== What Seiferas's paper describes ===\n");
    println!("At each stage t, apply separator to ALL bags where (t+level)%2 = 0.");
    println!("This means multiple levels are processed in each stage:\n");

    for t in 0..8 {
        let active: Vec<usize> = (0..=max_level)
            .filter(|&l| (t + l) % 2 == 0)
            .collect();
        let bags: Vec<String> = active.iter().flat_map(|&l| {
            let bs = n >> l;
            let nb = 1 << l;
            (0..nb).filter_map(move |idx| {
                let start = idx * bs;
                if start + bs <= n && bs > 1 {
                    Some(format!("L{}[{},{})", l, start, start + bs))
                } else {
                    None
                }
            })
        }).collect();
        println!("Stage {}: active levels = {:?}", t, active);
        println!("         bags processed: {}", bags.join(", "));
    }

    println!("\n=== The Mismatch ===\n");
    println!("Let's count how many times each level gets processed in 8 stages:\n");

    println!("{:>6} | Current (separatorStage) | Seiferas (alternating)", "Level");
    println!("-------+-------------------------+------------------------");
    for l in 0..=max_level {
        let current_count = if l < max_level { 1 } else { 0 };
        let seiferas_count = (0..8).filter(|&t| (t + l) % 2 == 0).count();
        println!("{:>6} | {:>23} | {:>22}", l, current_count, seiferas_count);
    }

    println!("\n=== Why This Matters ===\n");
    println!("With an IMPERFECT separator (ε > 0):");
    println!("  Each application of the separator introduces ~ε fraction errors.");
    println!("  But it also REDUCES existing errors multiplicatively.");
    println!("  After k applications to the same level:");
    println!("    stranger_count ≤ (some_factor)^k * initial_count");
    println!("  With k = 1 (current): errors from one pass remain.");
    println!("  With k = T/2 (Seiferas): errors shrink exponentially → 0.");
    println!();
    println!("With a PERFECT separator (ε = 0):");
    println!("  Stage 0 sorts the whole array → output is sorted.");
    println!("  Current code works fine with just 1 stage.");
    println!("  (Confirmed by Rust test: all 65536 binary inputs pass at n=16.)");

    println!("\n=== Concrete Impact ===\n");
    println!("The current separatorSortingNetwork is a valid sorting network");
    println!("ONLY when the separator perfectly sorts each chunk (ε = 0).");
    println!("For any real separator with ε > 0, the network doesn't sort.");
    println!();
    println!("The fix: change separatorStage or separatorSortingNetwork to");
    println!("process levels repeatedly. Two options:");
    println!();
    println!("Option 1 (match Seiferas): each 'stage' processes all active levels.");
    println!("  separatorStage t = apply sep to each bag where (t+level)%2=0");
    println!("  Total depth = numStages * (maxLevel/2 + 1) * d_sep");
    println!();
    println!("Option 2 (cycle): stage t processes level (t mod (maxLevel+1)).");
    println!("  separatorStage t = apply sep to chunks of size n/2^(t mod (ml+1))");
    println!("  Total depth = numStages * d_sep");
    println!("  Each level processed numStages/(maxLevel+1) times.");
}
