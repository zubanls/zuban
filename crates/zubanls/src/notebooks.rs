use std::{collections::HashMap, ops::Range};

use anyhow::bail;
use lsp_types::Uri;
use vfs::PathWithScheme;

#[derive(Default)]
pub(crate) struct Notebooks(HashMap<Uri, Notebook>);

#[derive(Default)]
pub(crate) struct Notebook {
    cells: Vec<PathWithScheme>,
}

impl Notebooks {
    pub fn add_notebook(&mut self, notebook_uri: Uri) {
        self.0.insert(notebook_uri, Default::default());
    }

    pub fn close_notebook(&mut self, notebook_uri: Uri) {
        self.0.remove(&notebook_uri);
    }

    pub fn remove_cells(&mut self, notebook_uri: &Uri, range: Range<usize>) -> anyhow::Result<()> {
        let Some(notebook) = self.0.get_mut(notebook_uri) else {
            bail!("Expected a notebook for {notebook_uri:?}");
        };
        notebook.cells.drain(range.clone());
        Ok(())
    }

    pub fn add_cell_and_return_parent(
        &mut self,
        notebook_uri: &Uri,
        cell_path: PathWithScheme,
        at_nth_cell: usize,
    ) -> anyhow::Result<Option<PathWithScheme>> {
        let Some(notebook) = self.0.get_mut(notebook_uri) else {
            bail!("Expected a notebook for {notebook_uri:?}");
        };
        if at_nth_cell > notebook.cells.len() {
            bail!(
                "Expected to be able to insert a cell at index {at_nth_cell}, \
                 but had only {} entries",
                notebook.cells.len()
            );
        }
        notebook.cells.insert(at_nth_cell, cell_path.clone());
        Ok(if at_nth_cell > 0 {
            notebook.cells.get(at_nth_cell - 1).cloned()
        } else {
            None
        })
    }

    pub fn nth_cell(
        &mut self,
        notebook_uri: &Uri,
        index: usize,
    ) -> anyhow::Result<Option<PathWithScheme>> {
        let Some(notebook) = self.0.get_mut(notebook_uri) else {
            bail!("Expected a notebook for {notebook_uri:?}");
        };
        Ok(notebook.cells.get(index).cloned())
    }
}
