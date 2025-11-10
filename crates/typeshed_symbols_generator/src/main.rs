use config::ProjectOptions;
use zuban_python::{Mode, Project};

fn main() {
    let project = Project::without_watcher(ProjectOptions::default(), Mode::LanguageServer);
    project;
}
