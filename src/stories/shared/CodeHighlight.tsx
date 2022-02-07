import React from 'react';

const CodeHighlight: React.FC = ({ children }) => (
  <div
    style={{
      padding: '11px 1rem',
      margin: '1rem 0',
      background: '#FFFFFF',
      border: '1px solid #C9D9E8',
      overflow: 'auto'
    }}
  >
    {children}
  </div>
);

export default CodeHighlight;
