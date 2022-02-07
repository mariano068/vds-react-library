import { storiesOf } from '@storybook/react';
import React from 'react';
import { muiTheme } from 'storybook-addon-material-ui5';
import VdsPageTitleDefaultStory from '../snippets/VdsPageTitle.snippets';

import { version } from '../../../package.json';

storiesOf(`vds@${version}`, module)
  .addDecorator(muiTheme())
  .add('Page title', () => (
    <VdsPageTitleDefaultStory />
  ));
