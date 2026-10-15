fn main() {
    let job = timed::job();
    println!("{}", job.report());
    println!("{}", job.queue.len());
    println!("{:?}", timed::wait());
}
