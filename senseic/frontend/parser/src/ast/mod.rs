mod expr;

pub use expr::*;
use sensei_core::Span;

use crate::{
    StrId,
    cst::{NodeIdx, NodeKind, NodeView},
    lexer::TokenIdx,
};

#[derive(Debug, Clone, Copy)]
pub struct InitBlock<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> InitBlock<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::InitBlock => Some(Self { view }),
            _ => None,
        }
    }

    pub fn body(&self) -> BlockExpr<'cst> {
        BlockExpr::from_view(self.view)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RunBlock<'cst> {
    view: NodeView<'cst>,
}

impl<'cst> RunBlock<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::RunBlock => Some(Self { view }),
            _ => None,
        }
    }

    pub fn body(&self) -> BlockExpr<'cst> {
        BlockExpr::from_view(self.view)
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ConstDecl<'cst> {
    pub name: StrId,
    view: NodeView<'cst>,
    pub r#type: Option<Expr<'cst>>,
    pub assign: Expr<'cst>,
}

impl<'cst> ConstDecl<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        let NodeKind::ConstDecl { typed } = view.kind() else {
            return None;
        };
        let mut children = view.children();
        let name = children.next().and_then(NodeView::ident).expect("TODO: malformed");
        let r#type = if typed {
            Some(children.next().and_then(Expr::new).expect("TODO: malformed"))
        } else {
            None
        };
        let assign = children.next().and_then(Expr::new).expect("TODO: malformed");
        Some(Self { name, view, r#type, assign })
    }

    pub fn span(&self) -> Span<TokenIdx> {
        self.view.span()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ImportKind {
    As(StrId),
    All,
}

#[derive(Debug, Clone, Copy)]
pub struct Import<'cst> {
    pub root: StrId,
    pub next_path_node: Option<NodeIdx>,
    pub kind: Option<ImportKind>,
    view: NodeView<'cst>,
}

impl<'cst> Import<'cst> {
    fn new(view: NodeView<'cst>) -> Option<Self> {
        let (path_node, kind) = match view.kind() {
            NodeKind::ImportAsDecl => {
                let mut children = view.children();
                let path = children.next()?;
                let as_name = children.next()?.kind().as_ident()?;
                (path, Some(ImportKind::As(as_name)))
            }
            NodeKind::ImportDecl { glob } => (view, glob.then_some(ImportKind::All)),
            _ => return None,
        };
        let mut path_elements = path_node.children();
        let root = path_elements.next()?.kind().as_ident()?;
        let next_path_node = path_elements.next().map(NodeView::idx);
        Some(Self { root, next_path_node, kind, view })
    }

    pub fn node(&self) -> NodeView<'cst> {
        self.view
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TopLevelDef<'cst> {
    Init(InitBlock<'cst>),
    Run(RunBlock<'cst>),
    Const(ConstDecl<'cst>),
    Import(Import<'cst>),
}

#[derive(Debug, Clone, Copy)]
pub struct File<'cst>(NodeView<'cst>);

impl<'cst> File<'cst> {
    pub fn new(view: NodeView<'cst>) -> Option<Self> {
        match view.kind() {
            NodeKind::File => Some(Self(view)),
            _ => None,
        }
    }

    pub fn iter_defs(&self) -> impl Iterator<Item = TopLevelDef<'cst>> {
        self.0.children().map(|child| {
            if let Some(def) = ConstDecl::new(child) {
                return TopLevelDef::Const(def);
            }
            if let Some(def) = InitBlock::new(child) {
                return TopLevelDef::Init(def);
            }
            if let Some(def) = RunBlock::new(child) {
                return TopLevelDef::Run(def);
            }
            if let Some(def) = Import::new(child) {
                return TopLevelDef::Import(def);
            }
            panic!("unexpected top-level node kind: {:?}", child.kind())
        })
    }
}
