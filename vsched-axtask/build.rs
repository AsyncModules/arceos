fn main() {
    // let rq_cap: usize = option_env!("RQ_CAP").unwrap_or("1").parse().unwrap();
    // let smp: usize = option_env!("SMP").unwrap_or("1").parse().unwrap();
    // let arch = option_env!("AX_ARCH").unwrap_or("x86_64");
    // std::process::Command::new("git")
    //     .arg("clone")
    //     .arg("https://github.com/AsyncModules/vsched.git")
    //     .status()
    //     .expect("Clone vsched failed");
    // std::process::Command::new("make")
    //     .arg("-C")
    //     .arg("vsched")
    //     .arg(format!("ARCH={}", arch))
    //     .arg(format!("RQ_CAP={}", rq_cap))
    //     .arg(format!("SMP={}", smp))
    //     .arg("all")
    //     .status()
    //     .expect("Compile vsched failed");
    // println!("cargo:rerun-if-changed=src/*");
}
