import { defineConfig } from 'vitepress'
import { withMermaid } from 'vitepress-plugin-mermaid'
import mathjax3 from 'markdown-it-mathjax3'

// https://vitepress.dev/reference/site-config
export default withMermaid(
  defineConfig({
    title: 'Defense Trilemma',
    description:
      'Geometric limits of prompt-injection defense design — impossibility theorems, mechanized in Lean 4.',
    cleanUrls: true,
    lastUpdated: true,
    ignoreDeadLinks: true,

    markdown: {
      math: true,
      config: (md) => {
        md.use(mathjax3)
      },
    },

    themeConfig: {
      nav: [
        { text: 'Home', link: '/' },
        { text: 'Theorems', link: '/theorems/' },
        { text: 'Proof Structure', link: '/proofs/' },
        { text: 'Visualizations', link: '/visualizations/' },
        { text: 'Lean Artifact', link: '/lean-artifact' },
      ],

      sidebar: {
        '/': [
          {
            text: 'Overview',
            items: [
              { text: 'Introduction', link: '/' },
              { text: 'The Defense Trilemma', link: '/trilemma' },
              { text: 'Formal Framework', link: '/framework' },
              { text: 'Notation & Glossary', link: '/glossary' },
            ],
          },
          {
            text: 'Theorems',
            collapsed: false,
            items: [
              { text: 'All Theorems (index)', link: '/theorems/' },
              { text: 'T1 · Boundary Fixation', link: '/theorems/boundary-fixation' },
              { text: 'T2 · ε-Robust Constraint', link: '/theorems/eps-robust' },
              { text: 'T3 · Persistent Unsafe Region', link: '/theorems/persistent' },
              { text: 'Defense Dilemma (K*)', link: '/theorems/defense-dilemma' },
              { text: 'Discrete Impossibility', link: '/theorems/discrete' },
              { text: 'Continuous Relaxation (Tietze)', link: '/theorems/tietze' },
              { text: 'Multi-Turn Impossibility', link: '/theorems/multi-turn' },
              { text: 'Stochastic Impossibility', link: '/theorems/stochastic' },
              { text: 'Pipeline Degradation', link: '/theorems/pipeline' },
              { text: 'Meta-Theorem (Regularity → Spillover)', link: '/theorems/meta-theorem' },
              { text: 'Quantitative Volume Bounds', link: '/theorems/volume-bounds' },
            ],
          },
          {
            text: 'Proof Structure',
            collapsed: false,
            items: [
              { text: 'End-to-end Proof Map', link: '/proofs/' },
              { text: 'Five-step Boundary Proof', link: '/proofs/boundary-five-step' },
              { text: 'Lean Dependency Graph', link: '/proofs/lean-dependency-graph' },
              { text: 'From Discrete → Continuous', link: '/proofs/discrete-to-continuous' },
            ],
          },
          {
            text: 'Visualizations',
            collapsed: false,
            items: [
              { text: 'Gallery', link: '/visualizations/' },
              { text: 'Three-tier Escalation', link: '/visualizations/escalation' },
              { text: 'Trilemma Diagram', link: '/visualizations/trilemma' },
              { text: 'Pipeline Amplification', link: '/visualizations/pipeline' },
              { text: 'Steep Region & Cone', link: '/visualizations/steep-region' },
            ],
          },
          {
            text: 'Reference',
            collapsed: true,
            items: [
              { text: 'Lean Artifact', link: '/lean-artifact' },
              { text: 'Engineering Prescription', link: '/engineering' },
              { text: 'Limitations & Counter-examples', link: '/limitations' },
              { text: 'Citation', link: '/citation' },
            ],
          },
        ],
      },

      socialLinks: [
        { icon: 'github', link: 'https://github.com/mbhatt1/stuff' },
      ],

      footer: {
        message:
          'The Defense Trilemma · mechanically verified in Lean 4 (46 files, ≈360 theorems, 0 sorry).',
        copyright: 'Bhatt, Munshi, Narajala, Habler, Al-Kahfah, Huang, Webb, Gatto (2026)',
      },

      outline: { level: [2, 3] },
      search: { provider: 'local' },
    },
  }),
  {
    // Mermaid plugin options
    mermaid: {
      theme: 'neutral',
      securityLevel: 'loose',
      flowchart: { curve: 'basis', useMaxWidth: true },
      themeVariables: {
        primaryColor: '#eef3fb',
        primaryTextColor: '#1d2433',
        lineColor: '#4a5a7a',
        fontFamily: 'ui-sans-serif, system-ui, sans-serif',
      },
    },
    mermaidPlugin: {
      class: 'mermaid diagram',
    },
  }
)
