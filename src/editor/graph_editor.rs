use std::{any::Any, collections::HashMap};

use crate::store::Store;
use atlier::system::App;
use imgui::Ui;
use imnodes::EditorContext;
use lifec::RuntimeState;
use specs::{
    storage::DenseVecStorage, Component, Entities, Join, ReadStorage, System, WriteStorage,
};
use std::hash::Hash;

#[derive(Clone, Component)]
#[storage(DenseVecStorage)]
pub struct Editor<N, S>
where
    N: Sized + Any + Send + Sync + Hash + Clone,
    S: RuntimeState + Component + Into<Store<N>>,
{
    pub render_node: fn(&mut Self, &mut EditorContext, &Ui),
    pub store: Store<N>,
    state: Option<S>,
}

pub struct Graph<N, S>
where
    N: Sized + Any + Send + Sync + Hash + Clone,
    S: RuntimeState + Component + Into<Store<N>>,
{
    imnodes: imnodes::Context,
    editor_contexts: HashMap<u32, imnodes::EditorContext>,
    editors: HashMap<u32, Editor<N, S>>,
}

impl<'a, N, S> System<'a> for Graph<N, S>
where
    N: Sized + Any + Send + Sync + Hash + Clone,
    S: RuntimeState + Component + Into<Store<N>>,
{
    type SystemData = (
        Entities<'a>,
        ReadStorage<'a, S>,
        WriteStorage<'a, Editor<N, S>>,
    );

    fn run(&mut self, (entities, runtime_state, mut editors): Self::SystemData) {
        for e in entities.join() {
            // If an entity has an editor assigned but no editor context, create one now
            if let None = self.editor_contexts.get(&e.id()) {
                self.editor_contexts
                    .insert(e.id(), self.imnodes.create_editor());
            }

            // If an entity has an editor comonent and this graph doesn't have the editor, add it now
            if let (None, Some(editor)) = (self.editors.get(&e.id()), editors.get_mut(e)) {
                self.editors.insert(e.id(), editor.clone());
            }

            // If runtime_state S has been updated for entity, merge it with editors state
            if let (Some(editor), Some(runtime_state)) =
                (self.editors.get_mut(&e.id()), runtime_state.get(e))
            {
                if let Some(state) = editor.state.as_mut() {
                    *state = state.merge_with(runtime_state);
                    editor.store = <S as Into<Store<N>>>::into(state.clone());
                }
            }
        }
    }
}

impl<'a, N, S> App for Graph<N, S>
where
    N: Sized + Any + Send + Sync + Hash + Clone,
    S: RuntimeState + Component + Into<Store<N>>,
{
    fn name() -> &'static str {
        "Graoh"
    }

    fn show_editor(&mut self, ui: &Ui) {
        for (eid, mut editor_context) in self.editor_contexts.iter_mut() {
            if let Some(editor) = self.editors.get_mut(&eid) {
                (editor.render_node)(editor, &mut editor_context, ui);
            }
        }
    }
}
