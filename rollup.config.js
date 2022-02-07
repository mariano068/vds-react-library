import react from 'react';
import reactDom from 'react-dom';
import commonjs from 'rollup-plugin-commonjs';
import resolve from 'rollup-plugin-node-resolve';
import typescript from 'rollup-plugin-typescript2';
import pkg from './package.json';
import scss from 'rollup-plugin-scss';

export default {
    input: './src/index.tsx',
    output: [
        {
            file: pkg.main,
            format: 'cjs',
        },
        {
            file: pkg.module,
            format: 'es',
        },
    ],
    external: [
        'react',
        'react-dom',
        ...Object.keys(pkg.dependencies || {}),
        ...Object.keys(pkg.peerDependencies || {}),
    ],
    plugins: [
        scss(),
        resolve(),
        commonjs({
            include: 'node_modules/**',
            namedExports: {
                'node_modules/react/index.js': [
                    'cloneElement',
                    'createContext',
                    'Component',
                    'createElement',
                ],
                'node_modules/react-dom/index.js': ['render', 'hydrate'],
                'node_modules/react-is/index.js': [
                    'isElement',
                    'isFragment',
                    'isValidElementType',
                    'ForwardRef',
                    'Memo',
                ],
                'react/jsx-runtime': ['jsx', 'jsxs', 'Fragment'],
                'react/jsx-dev-runtime': ['jsx', 'jsxs', 'jsxDEV'],
            },
        }),
        typescript({
            typescript: require('typescript'),
        }),
    ],
}
