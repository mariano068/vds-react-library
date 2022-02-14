import React from 'react';
import { VdsPageTitle } from '../../vds/VdsPageTitle/VdsPageTitle';

export const BaseStoryLayout: React.FC<{ storyTitle: string }> = ({ storyTitle, children }) => {
  return (
    <div style={{ margin: '0 70px', fontFamily: 'Roboto' }}>
      <VdsPageTitle title={storyTitle} />
      {children}
    </div>
  )
};
