use crate::database::{Database, DirectoryOrFile};

pub fn global_import(database: &Database, name: &str) {
    python_import(database.workspaces.iter().map(|x| x.get_root()), name)
}

pub fn python_import<'a>(directories: impl Iterator<Item=&'a DirectoryOrFile>, name: &str) {
    for directory in directories {
        match directory {
            DirectoryOrFile::Directory(name, children) => {
                for child in children {
                    if child.get_name() == name {
                        todo!("matched import") 
                    }
                }
            }
            DirectoryOrFile::File(_, _) => {
                unreachable!()
            }
        }
    }
}
